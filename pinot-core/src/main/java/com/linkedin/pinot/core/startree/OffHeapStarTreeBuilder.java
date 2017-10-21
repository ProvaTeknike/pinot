/**
 * Copyright (C) 2014-2016 LinkedIn Corp. (pinot-core@linkedin.com)
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *         http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.linkedin.pinot.core.startree;

import com.google.common.base.Objects;
import com.google.common.collect.BiMap;
import com.google.common.collect.HashBiMap;
import com.linkedin.pinot.common.data.DateTimeFieldSpec;
import com.linkedin.pinot.common.data.DimensionFieldSpec;
import com.linkedin.pinot.common.data.FieldSpec;
import com.linkedin.pinot.common.data.MetricFieldSpec;
import com.linkedin.pinot.common.data.Schema;
import com.linkedin.pinot.common.data.TimeFieldSpec;
import com.linkedin.pinot.common.utils.Pairs.IntPair;
import com.linkedin.pinot.core.data.GenericRow;
import com.linkedin.pinot.core.segment.creator.impl.V1Constants;
import com.linkedin.pinot.core.startree.hll.HllUtil;
import it.unimi.dsi.fastutil.ints.Int2ObjectMap;
import java.io.BufferedOutputStream;
import java.io.DataOutputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.ByteOrder;
import java.nio.channels.FileChannel;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import org.apache.commons.io.FileUtils;
import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.tuple.Pair;
import org.joda.time.DateTime;
import org.json.JSONObject;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import xerial.larray.buffer.LBuffer;
import xerial.larray.buffer.LBufferAPI;
import xerial.larray.mmap.MMapBuffer;
import xerial.larray.mmap.MMapMode;


/**
 * Uses file to build the star tree. Each row is divided into dimension and metrics. Time is added
 * to dimension list.
 * We use the split order to build the tree. In most cases, split order will be ranked depending on
 * the cardinality (descending order).
 * Time column will be excluded or last entry in split order irrespective of its cardinality
 * This is a recursive algorithm where we branch on one dimension at every level.
 * <b>Psuedo algo</b>
 * <code>
 *
 * build(){
 *  let table(1,N) consists of N input rows
 *  table.sort(1,N) //sort the table on all dimensions, according to split order
 *  constructTree(table, 0, N, 0);
 * }
 * constructTree(table,start,end, level){
 *    splitDimensionName = dimensionsSplitOrder[level]
 *    groupByResult<dimName, length> = table.groupBy(dimensionsSplitOrder[level]); //returns the number of rows for each value in splitDimension
 *    int rangeStart = 0;
 *    for each ( entry<dimName,length> groupByResult){
 *      if(entry.length > minThreshold){
 *        constructTree(table, rangeStart, rangeStart + entry.length, level +1);
 *      }
 *      rangeStart = rangeStart + entry.length;
 *      updateStarTree() //add new child
 *    }
 *
 *    //create a star tree node
 *
 *    aggregatedRows = table.uniqueAfterRemovingAttributeAndAggregateMetrics(start,end, splitDimensionName);
 *    for(each row in aggregatedRows_
 *    table.add(row);
 *    if(aggregateRows.size > minThreshold) {
 *      table.sort(end, end + aggregatedRows.size);
 *      constructStarTree(table, end, end + aggregatedRows.size, level +1);
 *    }
 * }
 * </code>
 */
public class OffHeapStarTreeBuilder implements StarTreeBuilder {
  private static final Logger LOG = LoggerFactory.getLogger(OffHeapStarTreeBuilder.class);

  // If the temporary buffer needed is larger than 500M, create a file and use MMapBuffer, otherwise use LBuffer
  private static final long MMAP_SIZE_THRESHOLD = 500_000_000;

  private File dataFile;
  private Schema schema;
  private DataOutputStream _dataOutputStream;
  int rawRecordCount = 0;
  int aggRecordCount = 0;
  private List<String> dimensionsSplitOrder;
  private Set<String> skipStarNodeCreationForDimensions;
  private Set<String> skipMaterializationForDimensions;

  private int maxLeafRecords;
  private StarTree starTree;
  private StarTreeIndexNode starTreeRootIndexNode;
  private int numDimensions;
  private int numMetrics;
  private List<String> dimensionNames;
  private List<String> metricNames;
  private String timeColumnName;
  private Map<String, Object> dimensionNameToStarValueMap;
  private HashBiMap<String, Integer> dimensionNameToIndexMap;
  private int _dimensionSize;
  private int _metricSize;
  private long _docSize;
  private File outDir;
  private Map<String, HashBiMap<Object, Integer>> dictionaryMap;

  boolean debugMode = false;
  private int[] _sortOrder;
  private int skipMaterializationCardinalityThreshold;
  private boolean enableOffHeapFormat;

  // Store data tables that need to be closed in close()
  private final List<StarTreeDataTable> _dataTablesToClose = new ArrayList<>();

  private static final boolean NEED_FLIP_ENDIANNESS = ByteOrder.nativeOrder() != ByteOrder.BIG_ENDIAN;

  /**
   * Flip the endianness of an int if needed.
   * <p>This is required to keep all the int as native order. (FileOutputStream always write int using BIG_ENDIAN)
   */
  private static int flipEndiannessIfNeeded(int value) {
    if (NEED_FLIP_ENDIANNESS) {
      return Integer.reverseBytes(value);
    } else {
      return value;
    }
  }

  public void init(StarTreeBuilderConfig builderConfig) throws Exception {
    schema = builderConfig.getSchema();
    timeColumnName = schema.getTimeColumnName();
    dimensionsSplitOrder = builderConfig.getDimensionsSplitOrder();
    skipStarNodeCreationForDimensions = builderConfig.getSkipStarNodeCreationForDimensions();
    skipMaterializationForDimensions = builderConfig.getSkipMaterializationForDimensions();
    skipMaterializationCardinalityThreshold = builderConfig.getSkipMaterializationCardinalityThreshold();
    enableOffHeapFormat = builderConfig.isEnableOffHeapFormat();
    maxLeafRecords = builderConfig.getMaxLeafRecords();
    outDir = builderConfig.getOutDir();
    if (outDir == null) {
      outDir = new File(System.getProperty("java.io.tmpdir"), V1Constants.STAR_TREE_INDEX_DIR + "_" + DateTime.now());
    }
    FileUtils.forceMkdir(outDir);
    LOG.info("Index output directory:{}", outDir);
    dataFile = new File(outDir, "star-tree.buf");
    LOG.info("StarTree output data file: {}", dataFile.getAbsolutePath());
    _dataOutputStream = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(dataFile)));

    dimensionNames = new ArrayList<>();
    dimensionNameToIndexMap = HashBiMap.create();
    dimensionNameToStarValueMap = new HashMap<>();
    dictionaryMap = new HashMap<>();

    // READ DIMENSIONS COLUMNS
    List<DimensionFieldSpec> dimensionFieldSpecs = schema.getDimensionFieldSpecs();
    for (int index = 0; index < dimensionFieldSpecs.size(); index++) {
      DimensionFieldSpec spec = dimensionFieldSpecs.get(index);
      String dimensionName = spec.getName();
      dimensionNames.add(dimensionName);
      dimensionNameToIndexMap.put(dimensionName, index);
      Object starValue;
      starValue = getAllStarValue(spec);
      dimensionNameToStarValueMap.put(dimensionName, starValue);
      HashBiMap<Object, Integer> dictionary = HashBiMap.create();
      dictionaryMap.put(dimensionName, dictionary);
    }
    // Treat DATE_TIME columns as dimensions, however we will never split on this dimension,
    // unless explicitly defined in split order
    List<DateTimeFieldSpec> dateTimeFieldSpecs = schema.getDateTimeFieldSpecs();
    for (int index = 0; index < dateTimeFieldSpecs.size(); index++) {
      DateTimeFieldSpec spec = dateTimeFieldSpecs.get(index);
      String dateTimeName = spec.getName();
      dimensionNames.add(dateTimeName);
      int size = dimensionNameToIndexMap.size();
      dimensionNameToIndexMap.put(dateTimeName, size);
      Object starValue;
      starValue = getAllStarValue(spec);
      dimensionNameToStarValueMap.put(dateTimeName, starValue);
      HashBiMap<Object, Integer> dictionary = HashBiMap.create();
      dictionaryMap.put(dateTimeName, dictionary);
    }
    // treat time column as just another dimension, only difference is that we will never split on
    // this dimension unless explicitly specified in split order
    if (timeColumnName != null) {
      dimensionNames.add(timeColumnName);
      TimeFieldSpec timeFieldSpec = schema.getTimeFieldSpec();
      int index = dimensionNameToIndexMap.size();
      dimensionNameToIndexMap.put(timeColumnName, index);
      Object starValue;
      starValue = getAllStarValue(timeFieldSpec);
      dimensionNameToStarValueMap.put(timeColumnName, starValue);
      HashBiMap<Object, Integer> dictionary = HashBiMap.create();
      dictionaryMap.put(schema.getTimeColumnName(), dictionary);
    }
    _dimensionSize = dimensionNames.size() * V1Constants.Numbers.INTEGER_SIZE;
    numDimensions = dimensionNames.size();

    // READ METRIC COLUMNS
    metricNames = new ArrayList<>();
    _metricSize = 0;
    for (MetricFieldSpec metricFieldSpec : schema.getMetricFieldSpecs()) {
      metricNames.add(metricFieldSpec.getName());
      _metricSize += metricFieldSpec.getFieldSize();
    }
    numMetrics = metricNames.size();

    _docSize = _dimensionSize + _metricSize;

    // INITIALIZE THE ROOT NODE
    this.starTreeRootIndexNode = new StarTreeIndexNode();
    this.starTreeRootIndexNode.setDimensionName(StarTreeIndexNodeInterf.ALL);
    this.starTreeRootIndexNode.setDimensionValue(StarTreeIndexNodeInterf.ALL);
    this.starTreeRootIndexNode.setLevel(0);
    LOG.info("dimensionNames:{}", dimensionNames);
    LOG.info("metricNames:{}", metricNames);
  }

  private Object getAllStarValue(FieldSpec spec) throws Exception {
    switch (spec.getDataType()) {
      case STRING:
        return "ALL";
      case BOOLEAN:
      case BYTE:
      case CHAR:
      case DOUBLE:
      case FLOAT:
      case INT:
      case LONG:
        return spec.getDefaultNullValue();
      case OBJECT:
      case SHORT:
      case DOUBLE_ARRAY:
      case CHAR_ARRAY:
      case FLOAT_ARRAY:
      case INT_ARRAY:
      case LONG_ARRAY:
      case SHORT_ARRAY:
      case STRING_ARRAY:
      case BYTE_ARRAY:
      default:
        throw new Exception("Unsupported dimension data type" + spec);
    }
  }

  public GenericRow toGenericRow(DimensionBuffer dimensionKey, MetricBuffer metricsHolder) {
    GenericRow row = new GenericRow();
    Map<String, Object> map = new HashMap<>();
    for (int i = 0; i < dimensionNames.size(); i++) {
      String dimName = dimensionNames.get(i);
      BiMap<Integer, Object> inverseDictionary = dictionaryMap.get(dimName).inverse();
      Object dimValue = inverseDictionary.get(dimensionKey.getDimension(i));
      if (dimValue == null) {
        dimValue = dimensionNameToStarValueMap.get(dimName);
      }
      map.put(dimName, dimValue);
    }
    for (int i = 0; i < numMetrics; i++) {
      String metName = metricNames.get(i);
      map.put(metName, metricsHolder.getValueConformToDataType(i));
    }
    row.init(map);
    return row;
  }

  public void append(GenericRow row) throws Exception {
    DimensionBuffer dimension = new DimensionBuffer(numDimensions);
    for (int i = 0; i < dimensionNames.size(); i++) {
      String dimName = dimensionNames.get(i);
      Map<Object, Integer> dictionary = dictionaryMap.get(dimName);
      Object dimValue = row.getValue(dimName);
      if (dimValue == null) {
        // TODO: Have another default value to represent STAR. Using default value to represent STAR
        // as of now.
        // It does not matter during query execution, since we know that values is STAR from the
        // star tree
        dimValue = dimensionNameToStarValueMap.get(dimName);
      }
      if (!dictionary.containsKey(dimValue)) {
        dictionary.put(dimValue, dictionary.size());
      }
      dimension.setDimension(i, dictionary.get(dimValue));
    }
    // initialize raw data row
    Object[] metrics = new Object[numMetrics];
    for (int i = 0; i < numMetrics; i++) {
      String metName = metricNames.get(i);
      if (schema.getMetricFieldSpecs().get(i).getDerivedMetricType() == MetricFieldSpec.DerivedMetricType.HLL) {
        // hll field is in string format, convert it to hll data type first
        metrics[i] = HllUtil.convertStringToHll((String) row.getValue(metName));
      } else {
        // no conversion for standard data types
        metrics[i] = row.getValue(metName);
      }
    }
    MetricBuffer metricBuffer = new MetricBuffer(metrics, schema.getMetricFieldSpecs());
    appendToRawBuffer(dimension, metricBuffer);
  }

  private void appendToRawBuffer(DimensionBuffer dimension, MetricBuffer metrics) throws IOException {
    appendToBuffer(dimension, metrics);
    rawRecordCount++;
  }

  private void appendToAggBuffer(DimensionBuffer dimension, MetricBuffer metrics) throws IOException {
    appendToBuffer(dimension, metrics);
    aggRecordCount++;
  }

  private void appendToBuffer(DimensionBuffer dimensions, MetricBuffer metricHolder) throws IOException {
    for (int i = 0; i < numDimensions; i++) {
      _dataOutputStream.writeInt(flipEndiannessIfNeeded(dimensions.getDimension(i)));
    }
    _dataOutputStream.write(metricHolder.toBytes(_metricSize));
  }

  public void build() throws Exception {
    if (skipMaterializationForDimensions == null) {
      skipMaterializationForDimensions = computeDefaultDimensionsToSkipMaterialization();
    }

    // For default split order, give preference to skipMaterializationForDimensions.
    // For user-defined split order, give preference to split-order.
    if (dimensionsSplitOrder == null || dimensionsSplitOrder.isEmpty()) {
      dimensionsSplitOrder = computeDefaultSplitOrder();
    } else {
      skipMaterializationForDimensions.removeAll(dimensionsSplitOrder);
    }

    LOG.info("Split order: {}", dimensionsSplitOrder);
    LOG.info("Skip Materialization For Dimensions: {}", skipMaterializationForDimensions);

    // Compute the sort order
    _sortOrder = new int[dimensionNames.size()];
    // Add dimensions in the split order first
    int index = 0;
    for (String dimensionName : dimensionsSplitOrder) {
      _sortOrder[index++] = dimensionNameToIndexMap.get(dimensionName);
    }
    // Add dimensions that are not part of dimensionsSplitOrder or skipMaterializationForDimensions
    for (String dimensionName : dimensionNames) {
      if (!dimensionsSplitOrder.contains(dimensionName) && !skipMaterializationForDimensions.contains(dimensionName)) {
        _sortOrder[index++] = dimensionNameToIndexMap.get(dimensionName);
      }
    }
    // Add dimensions in the skipMaterializationForDimensions last
    // The reason for this is that, after sorting and replacing the value for dimensions not materialized to ALL, the
    // docs with same dimensions will be grouped together for aggregation
    for (String dimensionName : skipMaterializationForDimensions) {
      _sortOrder[index++] = dimensionNameToIndexMap.get(dimensionName);
    }

    long start = System.currentTimeMillis();
    _dataOutputStream.flush();
    if (!skipMaterializationForDimensions.isEmpty()) {
      // Remove the skip materialization dimensions
      removeSkipMaterializationDimensions();
      // Recursively construct the star tree
      constructStarTree(starTreeRootIndexNode, rawRecordCount, rawRecordCount + aggRecordCount, 0);
    } else {
      // Sort the documents
      try (StarTreeDataTable dataTable = new StarTreeDataTable(new MMapBuffer(dataFile, MMapMode.READ_WRITE),
          _dimensionSize, _metricSize, rawRecordCount)) {
        dataTable.sort(_sortOrder);
      }
      // Recursively construct the star tree
      constructStarTree(starTreeRootIndexNode, 0, rawRecordCount, 0);
    }

    // Split the leaf nodes on time column. This is only possible if we have not split on time-column name
    // yet, and time column is still preserved (ie not replaced by StarTreeNode.all()).
    if (timeColumnName != null && !skipMaterializationForDimensions.contains(timeColumnName)
        && !dimensionsSplitOrder.contains(timeColumnName)) {
      splitLeafNodesOnTimeColumn();
    }

    // Create aggregate rows for all nodes in the tree
    createAggDocForAllNodes(starTreeRootIndexNode);
    long end = System.currentTimeMillis();
    LOG.info("Took {} ms to build star tree index. Original records:{} Materialized record:{}", (end - start),
        rawRecordCount, aggRecordCount);
    starTree = new StarTree(starTreeRootIndexNode, dimensionNameToIndexMap);
    File treeBinary = new File(outDir, "star-tree.bin");

    if (enableOffHeapFormat) {
      LOG.info("Saving tree in off-heap binary format at: {} ", treeBinary);
      StarTreeSerDe.writeTreeOffHeapFormat(starTree, treeBinary);
    } else {
      LOG.info("Saving tree in on-heap binary at: {} ", treeBinary);
      StarTreeSerDe.writeTreeOnHeapFormat(starTree, treeBinary);
    }

    if (debugMode) {
      printTree(starTreeRootIndexNode, 0);
    }
    LOG.info("Finished build tree. out dir: {} ", outDir);
    _dataOutputStream.close();
  }

  private void removeSkipMaterializationDimensions() throws IOException {
    try (StarTreeDataTable dataTable = new StarTreeDataTable(new MMapBuffer(dataFile, MMapMode.READ_WRITE),
        _dimensionSize, _metricSize, rawRecordCount)) {
      dataTable.sort(_sortOrder);
      Iterator<Pair<byte[], byte[]>> iterator = dataTable.iterator();
      DimensionBuffer currentDimensions = null;
      MetricBuffer currentMetrics = null;
      while (iterator.hasNext()) {
        Pair<byte[], byte[]> next = iterator.next();
        byte[] dimensionBytes = next.getLeft();
        byte[] metricBytes = next.getRight();
        DimensionBuffer dimensions = DimensionBuffer.fromBytes(dimensionBytes);
        MetricBuffer metrics = MetricBuffer.fromBytes(metricBytes, schema.getMetricFieldSpecs());
        for (int i = 0; i < numDimensions; i++) {
          String dimensionName = dimensionNameToIndexMap.inverse().get(i);
          if (skipMaterializationForDimensions.contains(dimensionName)) {
            dimensions.setDimension(i, StarTreeIndexNodeInterf.ALL);
          }
        }

        if (currentDimensions == null) {
          currentDimensions = dimensions;
          currentMetrics = metrics;
        } else {
          if (dimensions.equals(currentDimensions)) {
            currentMetrics.aggregate(metrics);
          } else {
            appendToAggBuffer(currentDimensions, currentMetrics);
            currentDimensions = dimensions;
            currentMetrics = metrics;
          }
        }
      }
      appendToAggBuffer(currentDimensions, currentMetrics);
    }

    _dataOutputStream.flush();
  }

  /**
   * Create aggregated docs using BFS
   * @param node
   */
  private MetricBuffer createAggDocForAllNodes(StarTreeIndexNode node) throws IOException {
    MetricBuffer aggMetricBuffer = null;
    if (node.isLeaf()) {
      int startDocId = node.getStartDocumentId();
      int endDocId = node.getEndDocumentId();
      int numDocs = endDocId - startDocId;
      try (StarTreeDataTable dataTable = new StarTreeDataTable(
          new MMapBuffer(dataFile, startDocId * _docSize, numDocs * _docSize, MMapMode.READ_ONLY), _dimensionSize,
          _metricSize, numDocs)) {
        Iterator<Pair<byte[], byte[]>> iterator = dataTable.iterator();
        Pair<byte[], byte[]> first = iterator.next();
        aggMetricBuffer = MetricBuffer.fromBytes(first.getRight(), schema.getMetricFieldSpecs());
        while (iterator.hasNext()) {
          Pair<byte[], byte[]> next = iterator.next();
          MetricBuffer metricBuffer = MetricBuffer.fromBytes(next.getRight(), schema.getMetricFieldSpecs());
          aggMetricBuffer.aggregate(metricBuffer);
        }
      }
    } else {
      Iterator<StarTreeIndexNode> childrenIterator = node.getChildrenIterator();
      while (childrenIterator.hasNext()) {
        StarTreeIndexNode child = childrenIterator.next();
        MetricBuffer childMetricBuffer = createAggDocForAllNodes(child);
        // don't use the star node value to compute aggregate for the parent
        if (child.getDimensionValue() == StarTreeIndexNodeInterf.ALL) {
          continue;
        }
        if (aggMetricBuffer == null) {
          aggMetricBuffer = new MetricBuffer(childMetricBuffer);
        } else {
          aggMetricBuffer.aggregate(childMetricBuffer);
        }
      }
    }
    //compute the dimension values for this node using the path, can be optimized by passing the path in the method call.
    Map<Integer, Integer> pathValues = node.getPathValues();
    DimensionBuffer dimensionBuffer = new DimensionBuffer(numDimensions);
    for (int i = 0; i < numDimensions; i++) {
      if (pathValues.containsKey(i)) {
        dimensionBuffer.setDimension(i, pathValues.get(i));
      } else {
        dimensionBuffer.setDimension(i, StarTreeIndexNodeInterf.ALL);
      }
    }
    node.setAggregatedDocumentId(rawRecordCount + aggRecordCount);
    appendToAggBuffer(dimensionBuffer, aggMetricBuffer);
    return aggMetricBuffer;
  }

  /**
   * Helper method that visits each leaf node does the following:
   * - Re-orders the doc-id's corresponding to leaf node wrt time column.
   * - Create children nodes for each time value under this leaf node.
   * - Adds a new record with aggregated data for this leaf node.
   * @throws Exception
   */
  private void splitLeafNodesOnTimeColumn() throws IOException {
    Queue<StarTreeIndexNode> nodes = new LinkedList<>();
    nodes.add(starTreeRootIndexNode);
    while (!nodes.isEmpty()) {
      StarTreeIndexNode node = nodes.remove();
      if (node.isLeaf()) {
        // If we have time column, split on time column, helps in time based filtering
        if (timeColumnName != null) {
          int startDocId = node.getStartDocumentId();
          int endDocId = node.getEndDocumentId();
          int numDocs = endDocId - startDocId;
          try (StarTreeDataTable dataTable = new StarTreeDataTable(
              new MMapBuffer(dataFile, startDocId * _docSize, numDocs * _docSize, MMapMode.READ_WRITE), _dimensionSize,
              _metricSize, numDocs)) {
            int timeColumnIndex = dimensionNameToIndexMap.get(timeColumnName);
            dataTable.sort(getNewSortOrder(timeColumnIndex, node.getLevel()));
            Int2ObjectMap<IntPair> timeColumnRangeMap = dataTable.groupOnDimension(timeColumnIndex);

            node.setChildDimensionName(timeColumnIndex);
            node.setChildren(new HashMap<Integer, StarTreeIndexNode>());

            for (int timeValue : timeColumnRangeMap.keySet()) {
              IntPair range = timeColumnRangeMap.get(timeValue);
              StarTreeIndexNode child = new StarTreeIndexNode();
              child.setDimensionName(timeColumnIndex);
              child.setDimensionValue(timeValue);
              child.setParent(node);
              child.setLevel(node.getLevel() + 1);
              child.setStartDocumentId(startDocId + range.getLeft());
              child.setEndDocumentId(startDocId + range.getRight());
              node.addChild(child, timeValue);
            }
          }
        }
      } else {
        Iterator<StarTreeIndexNode> childrenIterator = node.getChildrenIterator();
        while (childrenIterator.hasNext()) {
          nodes.add(childrenIterator.next());
        }
      }
    }
  }

  /**
   * Move the value in the sort order to the new index, keep the order of other values the same.
   */
  private int[] getNewSortOrder(int value, int newIndex) {
    int length = _sortOrder.length;
    int[] newSortOrder = new int[length];
    int sortOrderIndex = 0;
    for (int i = 0; i < length; i++) {
      if (i == newIndex) {
        newSortOrder[i] = value;
      } else {
        if (_sortOrder[sortOrderIndex] == value) {
          sortOrderIndex++;
        }
        newSortOrder[i] = _sortOrder[sortOrderIndex++];
      }
    }
    return newSortOrder;
  }

  /**
   * Debug method to print the tree.
   * @param node
   * @param level
   */
  private void printTree(StarTreeIndexNode node, int level) {
    for (int i = 0; i < level; i++) {
      LOG.info("  ");
    }
    BiMap<Integer, String> inverse = dimensionNameToIndexMap.inverse();
    String dimName = "ALL";
    Object dimValue = "ALL";
    if (node.getDimensionName() != StarTreeIndexNodeInterf.ALL) {
      dimName = inverse.get(node.getDimensionName());
    }
    if (node.getDimensionValue() != StarTreeIndexNodeInterf.ALL) {
      dimValue = dictionaryMap.get(dimName).inverse().get(node.getDimensionValue());
    }

    String formattedOutput = Objects.toStringHelper(node)
        .add("nodeId", node.getNodeId())
        .add("level", level)
        .add("dimensionName", dimName)
        .add("dimensionValue", dimValue)
        .add("childDimensionName", inverse.get(node.getChildDimensionName()))
        .add("childCount", node.getNumChildren())
        .add("startDocumentId", node.getStartDocumentId())
        .add("endDocumentId", node.getEndDocumentId())
        .add("documentCount", (node.getEndDocumentId() - node.getStartDocumentId()))
        .toString();
    LOG.info(formattedOutput);

    if (!node.isLeaf()) {
      Iterator<StarTreeIndexNode> childrenIterator = node.getChildrenIterator();
      while (childrenIterator.hasNext()) {
        printTree(childrenIterator.next(), level + 1);
      }
    }
  }

  private List<String> computeDefaultSplitOrder() {
    ArrayList<String> defaultSplitOrder = new ArrayList<>();
    // include only the dimensions, not time column and not the date_time columns. Also, assumes that
    // skipMaterializationForDimensions is built.
    for (String dimensionName : dimensionNames) {
      if (!skipMaterializationForDimensions.contains(dimensionName)) {
        defaultSplitOrder.add(dimensionName);
      }
    }
    if (timeColumnName != null) {
      defaultSplitOrder.remove(timeColumnName);
    }
    defaultSplitOrder.removeAll(schema.getDateTimeNames());
    Collections.sort(defaultSplitOrder, new Comparator<String>() {
      @Override
      public int compare(String o1, String o2) {
        return dictionaryMap.get(o2).size() - dictionaryMap.get(o1).size(); // descending
      }
    });
    return defaultSplitOrder;
  }

  private Set<String> computeDefaultDimensionsToSkipMaterialization() {
    Set<String> skipDimensions = new HashSet<>();
    for (String dimensionName : dimensionNames) {
      if (dictionaryMap.get(dimensionName).size() > skipMaterializationCardinalityThreshold) {
        skipDimensions.add(dimensionName);
      }
    }
    return skipDimensions;
  }

  private void printDataBuffer(LBufferAPI dataBuffer, int numDocsToPrint) throws IOException {
    try (StarTreeDataTable dataTable = new StarTreeDataTable(dataBuffer, _dimensionSize, _metricSize, numDocsToPrint)) {
      Iterator<Pair<byte[], byte[]>> iterator = dataTable.iterator();
      int counter = 0;
      while (iterator.hasNext()) {
        Pair<byte[], byte[]> next = iterator.next();
        LOG.info("{}, {}", DimensionBuffer.fromBytes(next.getLeft()),
            MetricBuffer.fromBytes(next.getRight(), schema.getMetricFieldSpecs()));
        if (counter++ == numDocsToPrint) {
          return;
        }
      }
    }
  }

  private int constructStarTree(StarTreeIndexNode node, int startDocId, int endDocId, int level) throws IOException {
    if (level == dimensionsSplitOrder.size()) {
      return 0;
    }

    int docsAdded = 0;
    String splitDimensionName = dimensionsSplitOrder.get(level);
    int splitDimensionId = dimensionNameToIndexMap.get(splitDimensionName);
    LOG.debug("Building tree at level:{} from startDoc:{} endDocId:{} splitting on dimension:{}", level, startDocId,
        endDocId, splitDimensionName);

    int numDocs = endDocId - startDocId;
    Int2ObjectMap<IntPair> dimensionRangeMap;
    try (StarTreeDataTable dataTable = new StarTreeDataTable(
        new MMapBuffer(dataFile, startDocId * _docSize, numDocs * _docSize, MMapMode.READ_ONLY), _dimensionSize,
        _metricSize, numDocs)) {
      dimensionRangeMap = dataTable.groupOnDimension(splitDimensionId);
    }
    LOG.debug("Group stats:{}", dimensionRangeMap);
    node.setChildDimensionName(splitDimensionId);
    node.setChildren(new HashMap<Integer, StarTreeIndexNode>());
    for (int childDimensionValue : dimensionRangeMap.keySet()) {
      StarTreeIndexNode child = new StarTreeIndexNode();
      child.setDimensionName(splitDimensionId);
      child.setDimensionValue(childDimensionValue);
      child.setParent(node);
      child.setLevel(node.getLevel() + 1);

      // n.b. We will number the nodes later using BFS after fully split

      // Add child to parent
      node.addChild(child, childDimensionValue);

      int childDocs = 0;
      IntPair range = dimensionRangeMap.get(childDimensionValue);
      int childStartDocId = range.getLeft() + startDocId;
      int childEndDocId = range.getRight() + startDocId;
      if (childEndDocId - childStartDocId > maxLeafRecords) {
        childDocs = constructStarTree(child, childStartDocId, childEndDocId, level + 1);
        docsAdded += childDocs;
      }

      // Either range <= maxLeafRecords, or we did not split further (last level).
      if (childDocs == 0) {
        child.setStartDocumentId(childStartDocId);
        child.setEndDocumentId(childEndDocId);
      }
    }

    // Return if star node does not need to be created.
    if (skipStarNodeCreationForDimensions != null && skipStarNodeCreationForDimensions.contains(splitDimensionName)) {
      return docsAdded;
    }

    // create star node
    StarTreeIndexNode starChild = new StarTreeIndexNode();
    starChild.setDimensionName(splitDimensionId);
    starChild.setDimensionValue(StarTreeIndexNodeInterf.ALL);
    starChild.setParent(node);
    starChild.setLevel(node.getLevel() + 1);
    // n.b. We will number the nodes later using BFS after fully split

    // Add child to parent
    node.addChild(starChild, StarTreeIndexNodeInterf.ALL);

    Iterator<Pair<DimensionBuffer, MetricBuffer>> iterator =
        getUniqueCombinations(startDocId, endDocId, splitDimensionId);
    int rowsAdded = 0;
    int startOffset = rawRecordCount + aggRecordCount;
    while (iterator.hasNext()) {
      Pair<DimensionBuffer, MetricBuffer> next = iterator.next();
      DimensionBuffer dimension = next.getLeft();
      MetricBuffer metricsHolder = next.getRight();
      LOG.debug("Adding row:{}", dimension);
      appendToAggBuffer(dimension, metricsHolder);
      rowsAdded++;
    }
    docsAdded += rowsAdded;
    LOG.debug("level {}, input docs:{},  additional records {}, aggRecordCount:{}", level, numDocs, rowsAdded,
        aggRecordCount);
    // flush
    _dataOutputStream.flush();

    int childDocs = 0;
    if (rowsAdded > maxLeafRecords) {
      childDocs = constructStarTree(starChild, startOffset, startOffset + rowsAdded, level + 1);
      docsAdded += childDocs;
    }

    // Either rowsAdded < maxLeafRecords, or we did not split further (last level).
    if (childDocs == 0) {
      starChild.setStartDocumentId(startOffset);
      starChild.setEndDocumentId(startOffset + rowsAdded);
    }

    return docsAdded;
  }

  /**
   * Get the unique combinations after removing a specified dimension.
   * <p>Here we assume the data file is already sorted.
   * <p>Aggregates the metrics for each unique combination.
   */
  private Iterator<Pair<DimensionBuffer, MetricBuffer>> getUniqueCombinations(int startDocId, int endDocId,
      int dimensionIdToRemove) throws IOException {
    LBufferAPI tempBuffer = null;
    int numDocs = endDocId - startDocId;
    long tempBufferSize = numDocs * _docSize;
    if (tempBufferSize > MMAP_SIZE_THRESHOLD) {
      // Create a temporary file and use MMapBuffer
      File tempFile = new File(outDir, startDocId + "_" + endDocId + ".unique.tmp");
      try (FileChannel src = new FileInputStream(dataFile).getChannel();
          FileChannel dest = new FileOutputStream(tempFile).getChannel()) {
        dest.transferFrom(src, startDocId * _docSize, tempBufferSize);
      }
      tempBuffer = new MMapBuffer(tempFile, MMapMode.READ_WRITE);
    } else {
      // Use LBuffer (direct memory buffer)
      MMapBuffer dataBuffer = null;
      try {
        tempBuffer = new LBuffer(tempBufferSize);
        dataBuffer = new MMapBuffer(dataFile, startDocId * _docSize, tempBufferSize, MMapMode.READ_ONLY);
        dataBuffer.copyTo(0, tempBuffer, 0, tempBufferSize);
      } catch (Exception e) {
        if (tempBuffer != null) {
          tempBuffer.release();
        }
        throw e;
      } finally {
        if (dataBuffer != null) {
          dataBuffer.close();
        }
      }
    }

    final StarTreeDataTable dataTable = new StarTreeDataTable(tempBuffer, _dimensionSize, _metricSize, numDocs);
    _dataTablesToClose.add(dataTable);
    dataTable.setDimensionValue(dimensionIdToRemove, StarTreeIndexNodeInterf.ALL);
    dataTable.sort(_sortOrder);

    return new Iterator<Pair<DimensionBuffer, MetricBuffer>>() {
      private final Iterator<Pair<byte[], byte[]>> _iterator = dataTable.iterator();
      private DimensionBuffer _currentDimensions;
      private MetricBuffer _currentMetrics;
      boolean _hasNext = true;

      @Override
      public boolean hasNext() {
        return _hasNext;
      }

      @Override
      public Pair<DimensionBuffer, MetricBuffer> next() {
        while (_iterator.hasNext()) {
          Pair<byte[], byte[]> next = _iterator.next();
          DimensionBuffer dimensions = DimensionBuffer.fromBytes(next.getLeft());
          MetricBuffer metrics = MetricBuffer.fromBytes(next.getRight(), schema.getMetricFieldSpecs());
          if (_currentDimensions == null) {
            _currentDimensions = dimensions;
            _currentMetrics = metrics;
          } else {
            if (dimensions.equals(_currentDimensions)) {
              _currentMetrics.aggregate(metrics);
            } else {
              ImmutablePair<DimensionBuffer, MetricBuffer> ret =
                  new ImmutablePair<>(_currentDimensions, _currentMetrics);
              _currentDimensions = dimensions;
              _currentMetrics = metrics;
              return ret;
            }
          }
        }
        _hasNext = false;
        closeDataTable(dataTable);
        return new ImmutablePair<>(_currentDimensions, _currentMetrics);
      }

      @Override
      public void remove() {
        throw new UnsupportedOperationException();
      }
    };
  }

  /**
   * Iterator to iterate over the records from startDocId to endDocId (exclusive)
   */
  @Override
  public Iterator<GenericRow> iterator(final int startDocId, final int endDocId) throws IOException {
    int numDocs = endDocId - startDocId;
    final StarTreeDataTable dataTable =
        new StarTreeDataTable(new MMapBuffer(dataFile, startDocId * _docSize, numDocs * _docSize, MMapMode.READ_ONLY),
            _dimensionSize, _metricSize, numDocs);
    _dataTablesToClose.add(dataTable);

    return new Iterator<GenericRow>() {
      private final Iterator<Pair<byte[], byte[]>> _iterator = dataTable.iterator();

      @Override
      public boolean hasNext() {
        boolean hasNext = _iterator.hasNext();
        if (!hasNext) {
          closeDataTable(dataTable);
        }
        return hasNext;
      }

      @Override
      public GenericRow next() {
        Pair<byte[], byte[]> pair = _iterator.next();
        DimensionBuffer dimensions = DimensionBuffer.fromBytes(pair.getLeft());
        MetricBuffer metrics = MetricBuffer.fromBytes(pair.getRight(), schema.getMetricFieldSpecs());
        return toGenericRow(dimensions, metrics);
      }

      @Override
      public void remove() {
        throw new UnsupportedOperationException();
      }
    };
  }

  private void closeDataTable(StarTreeDataTable dataTable) {
    try {
      dataTable.close();
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
    _dataTablesToClose.remove(dataTable);
  }

  public JSONObject getStarTreeAsJSON() throws Exception {
    JSONObject json = new JSONObject();
    toJson(json, starTreeRootIndexNode, dictionaryMap);
    return json;
  }

  private void toJson(JSONObject json, StarTreeIndexNode node, Map<String, HashBiMap<Object, Integer>> dictionaryMap)
      throws Exception {
    String dimName = "ALL";
    Object dimValue = "ALL";
    if (node.getDimensionName() != StarTreeIndexNodeInterf.ALL) {
      dimName = dimensionNames.get(node.getDimensionName());
    }
    if (node.getDimensionValue() != StarTreeIndexNodeInterf.ALL) {
      dimValue = dictionaryMap.get(dimName).inverse().get(node.getDimensionValue());
    }
    json.put("title", dimName + ":" + dimValue);
    Iterator<StarTreeIndexNode> childrenIterator = node.getChildrenIterator();

    if (childrenIterator != null) {
      JSONObject[] childJsons = new JSONObject[node.getNumChildren()];
      int index = 0;

      while (childrenIterator.hasNext()) {
        StarTreeIndexNode childNode = childrenIterator.next();
        JSONObject childJson = new JSONObject();
        toJson(childJson, childNode, dictionaryMap);
        childJsons[index++] = childJson;
      }
      json.put("nodes", childJsons);
    }
  }

  @Override
  public StarTree getTree() {
    return starTree;
  }

  @Override
  public int getTotalRawDocumentCount() {
    return rawRecordCount;
  }

  @Override
  public int getTotalAggregateDocumentCount() {
    return aggRecordCount;
  }

  @Override
  public int getMaxLeafRecords() {
    return maxLeafRecords;
  }

  @Override
  public List<String> getDimensionsSplitOrder() {
    return dimensionsSplitOrder;
  }

  public Map<String, HashBiMap<Object, Integer>> getDictionaryMap() {
    return dictionaryMap;
  }

  public HashBiMap<String, Integer> getDimensionNameToIndexMap() {
    return dimensionNameToIndexMap;
  }

  @Override
  public Set<String> getSkipMaterializationForDimensions() {
    return skipMaterializationForDimensions;
  }

  @Override
  public void close() throws IOException {
    for (StarTreeDataTable dataTable : _dataTablesToClose) {
      dataTable.close();
    }
    _dataTablesToClose.clear();
    FileUtils.deleteDirectory(outDir);
  }
}
