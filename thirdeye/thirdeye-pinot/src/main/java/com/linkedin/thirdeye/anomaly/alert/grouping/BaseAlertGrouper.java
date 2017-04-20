package com.linkedin.thirdeye.anomaly.alert.grouping;

import java.util.Collections;
import java.util.Map;

public abstract class BaseAlertGrouper<T> implements AlertGrouper<T> {
  protected Map<String, String> props = Collections.emptyMap();

  @Override
  public void setParameters(Map<String, String> props) {
    this.props = props;
  }
}