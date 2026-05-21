rm(list = ls())

# 0) Basic  

safe_var <- function(n, sx, sx2) {
  if (n <= 1L) return(0)
  max(sx2 / n - (sx / n)^2, 0)
}

rbind_fill <- function(dfs) {
  dfs <- Filter(Negate(is.null), dfs)
  if (length(dfs) == 0) return(data.frame())
  
  all_names <- unique(unlist(lapply(dfs, names)))
  
  aligned <- lapply(dfs, function(df) {
    missing <- setdiff(all_names, names(df))
    if (length(missing) > 0) {
      for (nm in missing) df[[nm]] <- NA
    }
    df <- df[, all_names, drop = FALSE]
    rownames(df) <- NULL
    df
  })
  
  do.call(rbind, aligned)
}

mean_na <- function(x) {
  if (all(is.na(x))) return(NA_real_)
  mean(x, na.rm = TRUE)
}

# 1) Scenarios and environment generation 

get_sim_scenarios <- function() {
  arm_names <- c("SafeBond", "RiskyCrash", "RiskyBoom")
  
  list(
    mean_shift = list(
      name = "Only_Mean_Shift",
      horizon = 10000,
      breakpoints = c(3001, 7001),
      arm_names = arm_names,
      means = rbind(
        c(0.020, 0.090, 0.045),
        c(0.020, 0.015, 0.075),
        c(0.020, 0.090, 0.045)
      ),
      sds = rbind(
        c(0.03, 0.08, 0.05),
        c(0.03, 0.08, 0.05),
        c(0.03, 0.08, 0.05)
      )
    ),
    
    var_shift = list(
      name = "Only_Variance_Shift",
      horizon = 10000,
      breakpoints = c(3001, 7001),
      arm_names = arm_names,
      means = rbind(
        c(0.020, 0.090, 0.045),
        c(0.020, 0.090, 0.045),
        c(0.020, 0.090, 0.045)
      ),
      sds = rbind(
        c(0.03, 0.05, 0.035),
        c(0.02, 0.08, 0.040),
        c(0.06, 0.05, 0.030)
      )
    ),
    
    mean_var_shift = list(
      name = "Mean_and_Variance_Shift",
      horizon = 10000,
      breakpoints = c(3001, 7001),
      arm_names = arm_names,
      means = rbind(
        c(0.020, 0.095, 0.045),
        c(0.020, 0.015, 0.075),
        c(0.020, 0.090, 0.045)
      ),
      sds = rbind(
        c(0.03, 0.07, 0.05),
        c(0.03, 0.15, 0.06),
        c(0.03, 0.08, 0.045)
      )
    )
  )
}

generate_piecewise_env <- function(horizon,
                                   breakpoints,
                                   means,
                                   sds,
                                   seed = NULL,
                                   arm_names = NULL) {
  if (!is.null(seed)) set.seed(seed)
  
  n_regimes <- nrow(means)
  n_arms <- ncol(means)
  
  if (is.null(arm_names)) {
    arm_names <- paste0("Arm", seq_len(n_arms))
  }
  
  if (length(breakpoints) != n_regimes - 1L) {
    stop("Number of breakpoints must equal number of regimes minus one.")
  }
  
  starts <- c(1, breakpoints)
  ends <- c(breakpoints - 1, horizon)
  
  regime <- integer(horizon)
  expected_matrix <- matrix(NA_real_, nrow = horizon, ncol = n_arms)
  sd_matrix <- matrix(NA_real_, nrow = horizon, ncol = n_arms)
  
  for (r in seq_len(n_regimes)) {
    idx <- starts[r]:ends[r]
    regime[idx] <- r
    
    expected_matrix[idx, ] <- matrix(
      means[r, ],
      nrow = length(idx),
      ncol = n_arms,
      byrow = TRUE
    )
    
    sd_matrix[idx, ] <- matrix(
      sds[r, ],
      nrow = length(idx),
      ncol = n_arms,
      byrow = TRUE
    )
  }
  
  rewards <- matrix(NA_real_, nrow = horizon, ncol = n_arms)
  colnames(rewards) <- arm_names
  
  for (k in seq_len(n_arms)) {
    rewards[, k] <- rnorm(
      horizon,
      mean = expected_matrix[, k],
      sd = sd_matrix[, k]
    )
  }
  
  list(
    horizon = horizon,
    n_arms = n_arms,
    regime = regime,
    arm_names = arm_names,
    rewards = rewards,
    expected_matrix = expected_matrix,
    sd_matrix = sd_matrix
  )
}

# 2) Mean-variance oracle and detection  

compute_mv_scores <- function(env, rho) {
  # Lower-is-better mean-variance loss:
  # MV_i = sigma_i^2 - rho * mu_i
  (env$sd_matrix ^ 2) - rho * env$expected_matrix
}

compute_mv_utility_scores <- function(env, rho) {
  # Higher-is-better equivalent:
  # U_i = rho * mu_i - sigma_i^2
  rho * env$expected_matrix - (env$sd_matrix ^ 2)
}

compute_ra_scores <- function(env, rho) {
  compute_mv_utility_scores(env, rho)
}

compute_dynamic_oracle <- function(env, rho, switching_cost = 0) {
  u_mat <- compute_mv_utility_scores(env, rho)
  mv_mat <- compute_mv_scores(env, rho)
  
  Tt <- env$horizon
  K <- env$n_arms
  
  dp <- matrix(-Inf, nrow = Tt, ncol = K)
  parent <- matrix(NA_integer_, nrow = Tt, ncol = K)
  
  dp[1, ] <- u_mat[1, ]
  
  for (t in 2:Tt) {
    for (i in seq_len(K)) {
      cand <- dp[t - 1, ] - switching_cost * ((seq_len(K)) != i)
      best_prev <- which.max(cand)
      dp[t, i] <- u_mat[t, i] + cand[best_prev]
      parent[t, i] <- best_prev
    }
  }
  
  oracle_id <- integer(Tt)
  oracle_id[Tt] <- which.max(dp[Tt, ])
  
  if (Tt >= 2) {
    for (t in (Tt - 1):1) {
      oracle_id[t] <- parent[t + 1, oracle_id[t + 1]]
    }
  }
  
  oracle_switch <- c(0L, as.integer(diff(oracle_id) != 0))
  oracle_u <- u_mat[cbind(seq_len(Tt), oracle_id)]
  oracle_mv <- mv_mat[cbind(seq_len(Tt), oracle_id)]
  oracle_inst_net <- oracle_u - switching_cost * oracle_switch
  
  list(
    oracle_id = oracle_id,
    oracle_name = env$arm_names[oracle_id],
    oracle_mv = oracle_mv,
    oracle_u = oracle_u,
    oracle_switch = oracle_switch,
    oracle_inst_net = oracle_inst_net,
    oracle_cum_net = cumsum(oracle_inst_net),
    pointwise_best_id = max.col(u_mat, ties.method = "first"),
    pointwise_best_value = apply(u_mat, 1, max),
    pointwise_min_mv_id = max.col(-mv_mat, ties.method = "first"),
    pointwise_min_mv_value = apply(mv_mat, 1, min)
  )
}

evaluate_alarm_metrics <- function(alarm_vec,
                                   breakpoints,
                                   horizon,
                                   detect_window = 250) {
  alarm_times <- which(alarm_vec == 1L)
  total_alarms <- length(alarm_times)
  
  if (total_alarms == 0) {
    return(list(
      total_alarms = 0L,
      false_alarms = 0L,
      false_alarm_rate = 0,
      detected_breaks = 0L,
      mean_detection_delay = NA_real_
    ))
  }
  
  used_alarm <- rep(FALSE, total_alarms)
  delays <- c()
  detected <- 0L
  
  for (b in breakpoints) {
    idx <- which(
      !used_alarm &
        alarm_times >= b &
        alarm_times <= min(horizon, b + detect_window)
    )
    
    if (length(idx) > 0) {
      first_idx <- idx[1]
      used_alarm[first_idx] <- TRUE
      delays <- c(delays, alarm_times[first_idx] - b)
      detected <- detected + 1L
    }
  }
  
  false_alarms <- sum(!used_alarm)
  
  list(
    total_alarms = total_alarms,
    false_alarms = false_alarms,
    false_alarm_rate = false_alarms / total_alarms,
    detected_breaks = detected,
    mean_detection_delay = if (length(delays) > 0) mean(delays) else NA_real_
  )
}

# 3) CUSUM change detection utilities 

cusum_init <- function(M = 40,
                       epsilon = 0.004,
                       h = 0.12) {
  list(
    M = M,
    epsilon = epsilon,
    h = h,
    n = 0L,
    ref_buffer = numeric(0),
    ref_mean = NA_real_,
    g_plus = 0,
    g_minus = 0
  )
}

cusum_update <- function(state, y) {
  state$n <- state$n + 1L
  
  if (is.na(state$ref_mean)) {
    state$ref_buffer <- c(state$ref_buffer, y)
    
    if (length(state$ref_buffer) >= state$M) {
      state$ref_mean <- mean(state$ref_buffer)
      state$ref_buffer <- numeric(0)
    }
    
    return(list(state = state, alarm = 0L))
  }
  
  s_plus <- y - state$ref_mean - state$epsilon
  s_minus <- state$ref_mean - y - state$epsilon
  
  state$g_plus <- max(0, state$g_plus + s_plus)
  state$g_minus <- max(0, state$g_minus + s_minus)
  
  alarm <- as.integer(state$g_plus >= state$h || state$g_minus >= state$h)
  
  list(state = state, alarm = alarm)
}

# 4) Evaluation and summary  

finalise_run_df <- function(env,
                            chosen_arm_id,
                            chosen_arm,
                            reward,
                            switched,
                            switching_cost,
                            rho,
                            oracle = NULL,
                            extra_cols = list()) {
  h <- env$horizon
  idx <- cbind(seq_len(h), chosen_arm_id)
  
  mu_chosen <- env$expected_matrix[idx]
  sigma2_chosen <- (env$sd_matrix[idx])^2
  
  mv_loss_chosen <- sigma2_chosen - rho * mu_chosen
  mv_utility_chosen <- rho * mu_chosen - sigma2_chosen
  
  cost_paid <- switching_cost * switched
  
  realised_mv_utility_net <- rho * reward - sigma2_chosen - cost_paid
  expected_mv_utility_net <- mv_utility_chosen - cost_paid
  
  raw_net_return <- reward - cost_paid
  
  gross_return <- pmax(1 + raw_net_return, 1e-8)
  log_wealth <- cumsum(log(gross_return))
  wealth_index <- exp(log_wealth)
  
  pointwise_best_mean_id <- max.col(env$expected_matrix, ties.method = "first")
  pointwise_best_mean_value <- apply(env$expected_matrix, 1, max)
  instant_regret_mean <- pointwise_best_mean_value - mu_chosen
  
  if (is.null(oracle)) {
    oracle <- compute_dynamic_oracle(env, rho, switching_cost)
  }
  
  instant_regret_mv_sc <- oracle$oracle_inst_net - expected_mv_utility_net
  
  out <- data.frame(
    t = seq_len(h),
    regime = env$regime,
    
    chosen_arm_id = chosen_arm_id,
    chosen_arm = chosen_arm,
    
    reward = reward,
    switched = switched,
    cost_paid = cost_paid,
    
    mu_chosen = mu_chosen,
    sigma2_chosen = sigma2_chosen,
    mv_loss_chosen = mv_loss_chosen,
    mv_utility_chosen = mv_utility_chosen,
    
    raw_net_return = raw_net_return,
    gross_return = gross_return,
    log_wealth = log_wealth,
    wealth_index = wealth_index,
    
    realised_mv_utility_net = realised_mv_utility_net,
    expected_mv_utility_net = expected_mv_utility_net,
    
    pointwise_best_mean_id = pointwise_best_mean_id,
    pointwise_best_mv_id = oracle$pointwise_best_id,
    dynamic_oracle_id = oracle$oracle_id,
    dynamic_oracle_inst_net = oracle$oracle_inst_net,
    
    instant_regret_mean = instant_regret_mean,
    instant_regret_mv_sc = instant_regret_mv_sc,
    
    stringsAsFactors = FALSE
  )
  
  if (length(extra_cols) > 0) {
    for (nm in names(extra_cols)) {
      out[[nm]] <- extra_cols[[nm]]
    }
  }
  
  out$cum_reward <- cumsum(out$reward)
  out$cum_cost_paid <- cumsum(out$cost_paid)
  out$cum_realised_mv_utility_net <- cumsum(out$realised_mv_utility_net)
  out$cum_expected_mv_utility_net <- cumsum(out$expected_mv_utility_net)
  out$cum_regret_mv_sc <- cumsum(out$instant_regret_mv_sc)
  out$avg_regret_mv_sc <- out$cum_regret_mv_sc / out$t
  out$cum_regret_mean <- cumsum(out$instant_regret_mean)
  out$switches_to_date <- cumsum(out$switched)
  
  # Backward-compatible aliases.
  out$g_chosen <- out$mv_utility_chosen
  out$ra_net_value <- out$realised_mv_utility_net
  out$expected_ra_net <- out$expected_mv_utility_net
  out$pointwise_best_ra_id <- out$pointwise_best_mv_id
  out$instant_regret_ra_sc <- out$instant_regret_mv_sc
  out$cum_ra_net_value <- out$cum_realised_mv_utility_net
  out$cum_expected_ra_net <- out$cum_expected_mv_utility_net
  out$cum_regret_ra_sc <- out$cum_regret_mv_sc
  out$avg_regret_ra_sc <- out$avg_regret_mv_sc
  
  if ("alarm" %in% names(out)) {
    out$alarms_to_date <- cumsum(out$alarm)
  }
  
  out
}

summarise_sim_run <- function(run_df,
                              algorithm_name,
                              scenario_name,
                              seed,
                              breakpoints) {
  net_returns <- run_df$raw_net_return
  
  sharpe_net <- if (stats::sd(net_returns) > 0) {
    mean(net_returns) / stats::sd(net_returns)
  } else {
    NA_real_
  }
  
  alarm_stats <- if ("alarm" %in% names(run_df)) {
    evaluate_alarm_metrics(
      alarm_vec = run_df$alarm,
      breakpoints = breakpoints,
      horizon = nrow(run_df)
    )
  } else {
    list(
      total_alarms = NA_real_,
      false_alarms = NA_real_,
      false_alarm_rate = NA_real_,
      detected_breaks = NA_real_,
      mean_detection_delay = NA_real_
    )
  }
  
  final_cum_mv_utility_net <- tail(run_df$cum_realised_mv_utility_net, 1)
  final_cum_regret_mv_sc <- tail(run_df$cum_regret_mv_sc, 1)
  final_avg_regret_mv_sc <- final_cum_regret_mv_sc / nrow(run_df)
  
  data.frame(
    algorithm = algorithm_name,
    scenario = scenario_name,
    seed = seed,
    
    final_cum_mv_utility_net = final_cum_mv_utility_net,
    final_cum_regret_mv_sc = final_cum_regret_mv_sc,
    final_avg_regret_mv_sc = final_avg_regret_mv_sc,
    
    final_cum_ra_net_value = final_cum_mv_utility_net,
    final_cum_regret_ra_sc = final_cum_regret_mv_sc,
    final_avg_regret_ra_sc = final_avg_regret_mv_sc,
    
    final_cum_regret_mean = tail(run_df$cum_regret_mean, 1),
    
    terminal_log_wealth = tail(run_df$log_wealth, 1),
    terminal_wealth_index = tail(run_df$wealth_index, 1),
    sharpe_net = sharpe_net,
    
    total_switches = sum(run_df$switched),
    total_cost_paid = tail(run_df$cum_cost_paid, 1),
    
    oracle_share_dynamic = mean(run_df$chosen_arm_id == run_df$dynamic_oracle_id),
    oracle_share_pointwise_mv = mean(run_df$chosen_arm_id == run_df$pointwise_best_mv_id),
    oracle_share_pointwise_ra = mean(run_df$chosen_arm_id == run_df$pointwise_best_mv_id),
    
    total_alarms = alarm_stats$total_alarms,
    false_alarms = alarm_stats$false_alarms,
    false_alarm_rate = alarm_stats$false_alarm_rate,
    detected_breaks = alarm_stats$detected_breaks,
    mean_detection_delay = alarm_stats$mean_detection_delay,
    
    stringsAsFactors = FALSE
  )
}

# 5) Bandit policies 

run_ucb1_env <- function(env,
                         switching_cost = 0.005,
                         rho = 1,
                         oracle = NULL) {
  h <- env$horizon
  k <- env$n_arms
  
  N <- integer(k)
  X_sum <- numeric(k)
  
  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)
  
  prev_arm <- NA_integer_
  
  for (t in seq_len(h)) {
    if (t <= k) {
      arm_t <- t
    } else {
      scores <- (X_sum / N) + sqrt((2 * log(t)) / N)
      arm_t <- which.max(scores)
    }
    
    chosen_id[t] <- arm_t
    chosen_name[t] <- env$arm_names[arm_t]
    rew[t] <- env$rewards[t, arm_t]
    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)
    
    N[arm_t] <- N[arm_t] + 1L
    X_sum[arm_t] <- X_sum[arm_t] + rew[t]
    
    prev_arm <- arm_t
  }
  
  finalise_run_df(
    env = env,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    oracle = oracle
  )
}

run_swucb_env <- function(env,
                          alpha = 0.10,
                          tau = 700,
                          switching_cost = 0.005,
                          rho = 1,
                          oracle = NULL) {
  h <- env$horizon
  k <- env$n_arms
  
  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)
  
  hist_arms <- integer(h)
  hist_rews <- numeric(h)
  
  prev_arm <- NA_integer_
  
  for (t in seq_len(h)) {
    arm_t <- NA_integer_
    
    if (t <= k) {
      arm_t <- t
    } else {
      win_start <- max(1, t - tau)
      arms_w <- hist_arms[win_start:(t - 1)]
      rews_w <- hist_rews[win_start:(t - 1)]
      
      scores <- rep(-Inf, k)
      
      for (i in seq_len(k)) {
        mask <- arms_w == i
        nk <- sum(mask)
        
        if (nk == 0) {
          arm_t <- i
          break
        }
        
        scores[i] <- mean(rews_w[mask]) +
          sqrt(alpha * log(max(min(t, tau), 2)) / nk)
      }
      
      if (is.na(arm_t)) {
        arm_t <- which.max(scores)
      }
    }
    
    chosen_id[t] <- arm_t
    chosen_name[t] <- env$arm_names[arm_t]
    rew[t] <- env$rewards[t, arm_t]
    
    hist_arms[t] <- arm_t
    hist_rews[t] <- rew[t]
    
    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)
    prev_arm <- arm_t
  }
  
  finalise_run_df(
    env = env,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    oracle = oracle
  )
}

run_ducb_env <- function(env,
                         alpha = 0.10,
                         gamma = 0.998,
                         switching_cost = 0.005,
                         rho = 1,
                         oracle = NULL) {
  h <- env$horizon
  k <- env$n_arms
  
  N_g <- numeric(k)
  X_g <- numeric(k)
  n_g <- 0
  
  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)
  
  prev_arm <- NA_integer_
  
  for (t in seq_len(h)) {
    if (t <= k) {
      arm_t <- t
    } else {
      scores <- rep(-Inf, k)
      
      for (i in seq_len(k)) {
        if (N_g[i] > 1e-10) {
          scores[i] <- (X_g[i] / N_g[i]) +
            sqrt(alpha * log(max(n_g, 2)) / N_g[i])
        }
      }
      
      arm_t <- which.max(scores)
    }
    
    chosen_id[t] <- arm_t
    chosen_name[t] <- env$arm_names[arm_t]
    rew[t] <- env$rewards[t, arm_t]
    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)
    
    N_g <- gamma * N_g
    X_g <- gamma * X_g
    n_g <- gamma * n_g + 1
    
    N_g[arm_t] <- N_g[arm_t] + 1
    X_g[arm_t] <- X_g[arm_t] + rew[t]
    
    prev_arm <- arm_t
  }
  
  finalise_run_df(
    env = env,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    oracle = oracle
  )
}

run_cd_ucb_env <- function(env,
                           alpha = 0.015,
                           switching_cost = 0.005,
                           M = 40,
                           epsilon = 0.004,
                           h_thresh = 0.12,
                           rho = 1,
                           oracle = NULL) {
  h <- env$horizon
  k <- env$n_arms
  
  N <- integer(k)
  X_sum <- numeric(k)
  
  dets <- lapply(seq_len(k), function(i) {
    cusum_init(M, epsilon, h_thresh)
  })
  
  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)
  alarm_vec <- integer(h)
  forced_explore <- integer(h)
  
  prev_arm <- NA_integer_
  
  for (t in seq_len(h)) {
    if (t <= k) {
      arm_t <- t
    } else if (runif(1) < alpha) {
      arm_t <- sample.int(k, 1)
      forced_explore[t] <- 1L
    } else {
      scores <- rep(-Inf, k)
      
      for (i in seq_len(k)) {
        if (N[i] > 0) {
          scores[i] <- (X_sum[i] / N[i]) +
            sqrt(2 * log(max(sum(N), 2)) / N[i])
        }
      }
      
      arm_t <- which.max(scores)
    }
    
    chosen_id[t] <- arm_t
    chosen_name[t] <- env$arm_names[arm_t]
    rew[t] <- env$rewards[t, arm_t]
    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)
    
    det_out <- cusum_update(dets[[arm_t]], rew[t])
    dets[[arm_t]] <- det_out$state
    alarm_vec[t] <- det_out$alarm
    
    if (alarm_vec[t] == 1L) {
      N[arm_t] <- 1L
      X_sum[arm_t] <- rew[t]
      dets[[arm_t]] <- cusum_init(M, epsilon, h_thresh)
    } else {
      N[arm_t] <- N[arm_t] + 1L
      X_sum[arm_t] <- X_sum[arm_t] + rew[t]
    }
    
    prev_arm <- arm_t
  }
  
  finalise_run_df(
    env = env,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    oracle = oracle,
    extra_cols = list(
      alarm = alarm_vec,
      forced_explore = forced_explore
    )
  )
}

run_rs_sc_cusum_ucb_env <- function(env,
                                    alpha = 0.015,
                                    rho = 1,
                                    switching_cost = 0.005,
                                    barrier = 0,
                                    M = 40,
                                    epsilon = 0.004,
                                    h_thresh = 0.12,
                                    oracle = NULL) {
  h <- env$horizon
  k <- env$n_arms
  
  N <- integer(k)
  X_sum <- numeric(k)
  X2_sum <- numeric(k)
  
  det_m <- lapply(seq_len(k), function(i) {
    cusum_init(M, epsilon, h_thresh)
  })
  
  det_v <- lapply(seq_len(k), function(i) {
    cusum_init(M, epsilon, h_thresh)
  })
  
  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)
  
  alarm_vec <- integer(h)
  mean_alarm <- integer(h)
  var_alarm <- integer(h)
  forced_explore <- integer(h)
  
  prev_arm <- NA_integer_
  
  for (t in seq_len(h)) {
    if (t <= k) {
      arm_t <- t
    } else if (runif(1) < alpha) {
      arm_t <- sample.int(k, 1)
      forced_explore[t] <- 1L
    } else {
      scores <- rep(-Inf, k)
      
      for (i in seq_len(k)) {
        if (N[i] > 0) {
          mu_hat <- X_sum[i] / N[i]
          var_hat <- safe_var(N[i], X_sum[i], X2_sum[i])
          bonus_mu <- sqrt((2 * log(max(sum(N), 2))) / N[i])
          
          # Mean-variance index:
          score_i <- rho * (mu_hat + bonus_mu) - var_hat
          
          if (!is.na(prev_arm) && i != prev_arm) {
            score_i <- score_i - switching_cost - barrier
          }
          
          scores[i] <- score_i
        }
      }
      
      arm_t <- which.max(scores)
    }
    
    chosen_id[t] <- arm_t
    chosen_name[t] <- env$arm_names[arm_t]
    rew[t] <- env$rewards[t, arm_t]
    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)
    
    mu_pre <- ifelse(N[arm_t] > 0, X_sum[arm_t] / N[arm_t], 0)
    
    var_pre <- ifelse(
      N[arm_t] > 1,
      safe_var(N[arm_t], X_sum[arm_t], X2_sum[arm_t]),
      1e-6
    )
    
    mean_signal <- rew[t] - mu_pre
    var_signal <- (rew[t] - mu_pre)^2 - var_pre
    
    res_m <- cusum_update(det_m[[arm_t]], mean_signal)
    det_m[[arm_t]] <- res_m$state
    
    res_v <- cusum_update(det_v[[arm_t]], var_signal)
    det_v[[arm_t]] <- res_v$state
    
    mean_alarm[t] <- res_m$alarm
    var_alarm[t] <- res_v$alarm
    alarm_vec[t] <- as.integer(mean_alarm[t] == 1L || var_alarm[t] == 1L)
    
    if (alarm_vec[t] == 1L) {
      N[arm_t] <- 1L
      X_sum[arm_t] <- rew[t]
      X2_sum[arm_t] <- rew[t]^2
      
      det_m[[arm_t]] <- cusum_init(M, epsilon, h_thresh)
      det_v[[arm_t]] <- cusum_init(M, epsilon, h_thresh)
    } else {
      N[arm_t] <- N[arm_t] + 1L
      X_sum[arm_t] <- X_sum[arm_t] + rew[t]
      X2_sum[arm_t] <- X2_sum[arm_t] + rew[t]^2
    }
    
    prev_arm <- arm_t
  }
  
  finalise_run_df(
    env = env,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    oracle = oracle,
    extra_cols = list(
      alarm = alarm_vec,
      mean_alarm = mean_alarm,
      var_alarm = var_alarm,
      forced_explore = forced_explore
    )
  )
}

# 6) Plotting and aggregation 

POLICY_ORDER <- c(
  "UCB1",
  "SW-UCB",
  "D-UCB",
  "CUSUM-UCB",
  "RS-SC-CUSUM-UCB"
)

POLICY_COLS <- c(
  "UCB1" = "#E69F00",
  "SW-UCB" = "#009E73",
  "D-UCB" = "#56B4E9",
  "CUSUM-UCB" = "#D55E00",
  "RS-SC-CUSUM-UCB" = "#CC79A7"
)

add_y_padding <- function(y, pad_frac = 0.06) {
  y <- y[is.finite(y)]
  
  if (length(y) == 0) {
    return(c(0, 1))
  }
  
  yr <- range(y)
  span <- diff(yr)
  
  if (span == 0) {
    return(yr + c(-1, 1) * max(abs(yr[1]), 1) * pad_frac)
  }
  
  yr + c(-1, 1) * span * pad_frac
}

make_line_plot <- function(plot_df,
                           breakpoints,
                           ylab,
                           outfile,
                           legend_position = "topleft",
                           xlab = "Time",
                           show_legend = TRUE,
                           show_grid = TRUE) {
  dir.create(dirname(outfile), recursive = TRUE, showWarnings = FALSE)
  
  keep <- is.finite(plot_df$t) & is.finite(plot_df$mean)
  plot_df <- plot_df[keep, , drop = FALSE]
  
  if (nrow(plot_df) == 0) {
    warning(sprintf("Skipping plot because all values are non-finite: %s", outfile))
    return(invisible(NULL))
  }
  
  algs <- intersect(POLICY_ORDER, unique(plot_df$algorithm))
  extra_algs <- setdiff(unique(plot_df$algorithm), algs)
  algs <- c(algs, extra_algs)
  
  png(outfile, width = 1200, height = 750, res = 130)
  on.exit(dev.off(), add = TRUE)
  
  old_par <- par(no.readonly = TRUE)
  on.exit(par(old_par), add = TRUE)
  
  par(
    mar = c(4.5, 5.0, 1.0, 1.2),
    mgp = c(2.8, 0.8, 0),
    las = 1
  )
  
  plot(
    NA,
    xlim = range(plot_df$t, na.rm = TRUE),
    ylim = add_y_padding(plot_df$mean),
    xlab = xlab,
    ylab = ylab,
    main = "",
    cex.lab = 1.15,
    cex.axis = 1.0
  )
  
  if (show_grid) {
    grid(col = "grey88", lty = "dotted")
  }
  
  for (bp in breakpoints) {
    abline(v = bp, lty = 2, col = "grey45", lwd = 1.2)
  }
  
  for (alg in algs) {
    df <- plot_df[plot_df$algorithm == alg, , drop = FALSE]
    df <- df[order(df$t), ]
    
    if (nrow(df) == 0) next
    
    col_i <- if (alg %in% names(POLICY_COLS)) {
      POLICY_COLS[alg]
    } else {
      "grey40"
    }
    
    lines(
      df$t,
      df$mean,
      col = col_i,
      lwd = 2.2
    )
  }
  
  if (show_legend) {
    legend_cols <- ifelse(
      algs %in% names(POLICY_COLS),
      POLICY_COLS[algs],
      "grey40"
    )
    
    legend(
      legend_position,
      legend = algs,
      col = legend_cols,
      lwd = 2.2,
      bty = "n",
      cex = 0.95
    )
  }
  
  invisible(NULL)
}

make_chosen_arm_plot <- function(paths,
                                 breakpoints,
                                 outfile,
                                 seed = 1,
                                 show_panel_labels = TRUE) {
  dir.create(dirname(outfile), recursive = TRUE, showWarnings = FALSE)
  
  sub <- paths[paths$seed == seed, c("t", "algorithm", "chosen_arm_id")]
  algs <- intersect(POLICY_ORDER, unique(sub$algorithm))
  extra_algs <- setdiff(unique(sub$algorithm), algs)
  algs <- c(algs, extra_algs)
  
  png(outfile, width = 1200, height = 850, res = 130)
  on.exit(dev.off(), add = TRUE)
  
  old_par <- par(no.readonly = TRUE)
  on.exit(par(old_par), add = TRUE)
  
  par(
    mfrow = c(length(algs), 1),
    mar = c(2.6, 4.3, 0.6, 1.2),
    mgp = c(2.4, 0.8, 0),
    las = 1
  )
  
  for (alg in algs) {
    df <- sub[sub$algorithm == alg, ]
    df <- df[order(df$t), ]
    
    col_i <- if (alg %in% names(POLICY_COLS)) {
      POLICY_COLS[alg]
    } else {
      "grey40"
    }
    
    plot(
      df$t,
      df$chosen_arm_id,
      type = "s",
      xaxt = "n",
      xlab = "",
      ylab = "Arm",
      main = "",
      ylim = c(1, max(df$chosen_arm_id, na.rm = TRUE)),
      col = col_i,
      lwd = 1.8
    )
    
    grid(col = "grey90", lty = "dotted")
    
    for (bp in breakpoints) {
      abline(v = bp, lty = 2, col = "grey45", lwd = 1.1)
    }
    
    axis(2, at = sort(unique(df$chosen_arm_id)))
    
    if (show_panel_labels) {
      mtext(alg, side = 3, line = -0.2, adj = 0, cex = 0.85)
    }
  }
  
  axis(1)
  mtext("Time", side = 1, line = 1.8, outer = FALSE)
  
  invisible(NULL)
}

summarise_by_algorithm <- function(df_summary) {
  metric_cols <- c(
    "final_cum_mv_utility_net",
    "final_cum_regret_mv_sc",
    "final_avg_regret_mv_sc",
    "final_cum_regret_mean",
    "terminal_log_wealth",
    "terminal_wealth_index",
    "sharpe_net",
    "total_switches",
    "total_cost_paid",
    "oracle_share_dynamic",
    "oracle_share_pointwise_mv",
    "total_alarms",
    "false_alarms",
    "false_alarm_rate",
    "detected_breaks",
    "mean_detection_delay"
  )
  
  algs <- unique(df_summary$algorithm)
  
  out <- lapply(algs, function(alg) {
    sub <- df_summary[df_summary$algorithm == alg, , drop = FALSE]
    
    row <- data.frame(
      algorithm = alg,
      stringsAsFactors = FALSE
    )
    
    for (mc in metric_cols) {
      row[[mc]] <- mean_na(sub[[mc]])
    }
    
    row
  })
  
  agg <- do.call(rbind, out)
  agg <- agg[order(-agg$final_cum_mv_utility_net), ]
  rownames(agg) <- NULL
  agg
}

# 7) Monte Carlo

PATH_METRICS <- c(
  "cum_realised_mv_utility_net",
  "cum_regret_mv_sc",
  "avg_regret_mv_sc",
  "log_wealth",
  "cum_cost_paid"
)

init_path_accumulator <- function(horizon, algs, metrics = PATH_METRICS) {
  acc <- lapply(metrics, function(m) {
    matrix(
      0,
      nrow = horizon,
      ncol = length(algs),
      dimnames = list(NULL, algs)
    )
  })
  names(acc) <- metrics
  acc
}

update_path_accumulator <- function(acc, run_df, alg) {
  for (m in names(acc)) {
    acc[[m]][, alg] <- acc[[m]][, alg] + run_df[[m]]
  }
  acc
}

accumulator_to_plot_df <- function(acc_mat, n_seeds) {
  algs <- colnames(acc_mat)
  
  out <- lapply(algs, function(alg) {
    data.frame(
      t = seq_len(nrow(acc_mat)),
      algorithm = alg,
      mean = acc_mat[, alg] / n_seeds,
      stringsAsFactors = FALSE
    )
  })
  
  do.call(rbind, out)
}

extract_chosen_arm_path <- function(run_df, alg, seed, scenario_name) {
  data.frame(
    t = run_df$t,
    algorithm = alg,
    seed = seed,
    scenario = scenario_name,
    chosen_arm_id = run_df$chosen_arm_id,
    stringsAsFactors = FALSE
  )
}

extract_compact_path <- function(run_df, alg, seed, scenario_name) {
  data.frame(
    t = run_df$t,
    regime = run_df$regime,
    algorithm = alg,
    seed = seed,
    scenario = scenario_name,
    chosen_arm_id = run_df$chosen_arm_id,
    chosen_arm = run_df$chosen_arm,
    cum_realised_mv_utility_net = run_df$cum_realised_mv_utility_net,
    cum_regret_mv_sc = run_df$cum_regret_mv_sc,
    avg_regret_mv_sc = run_df$avg_regret_mv_sc,
    log_wealth = run_df$log_wealth,
    cum_cost_paid = run_df$cum_cost_paid,
    stringsAsFactors = FALSE
  )
}
  
run_full_simulation <- function(seeds = 1:1000,
                                  switching_cost = 0.005,
                                  rho = 1,
                                  rs_barrier = 0,
                                  cd_alpha = 0.015,
                                  cd_M = 40,
                                  cd_epsilon = 0.004,
                                  cd_h = 0.12,
                                  output_dir = "outputs",
                                  keep_path_seeds = seeds[1],
                                  save_compact_paths = FALSE,
                                  gc_every = 25) {
  
  scenarios <- get_sim_scenarios()
  all_results <- list()
  
  dir.create(output_dir, recursive = TRUE, showWarnings = FALSE)
  
  for (scen_key in names(scenarios)) {
    scenario <- scenarios[[scen_key]]
    
    cat("\n======================================================\n")
    cat(sprintf("STARTING SCENARIO: %s\n", scenario$name))
    cat("======================================================\n")
    
    scenario_dir <- file.path(output_dir, scenario$name)
    figures_dir <- file.path(scenario_dir, "figures")
    tables_dir <- file.path(scenario_dir, "tables")
    
    dir.create(scenario_dir, recursive = TRUE, showWarnings = FALSE)
    dir.create(figures_dir, recursive = TRUE, showWarnings = FALSE)
    dir.create(tables_dir, recursive = TRUE, showWarnings = FALSE)
    
    n_alg <- length(POLICY_ORDER)
    n_seed <- length(seeds)
    
    all_summary <- vector("list", n_seed * n_alg)
    summary_idx <- 1L
    
    path_acc <- init_path_accumulator(
      horizon = scenario$horizon,
      algs = POLICY_ORDER,
      metrics = PATH_METRICS
    )
    
    chosen_arm_paths <- list()
    chosen_idx <- 1L
    
    compact_paths <- list()
    compact_idx <- 1L
    
    for (s_idx in seq_along(seeds)) {
      seed <- seeds[s_idx]
      
      if (s_idx %% 10 == 1 || s_idx == n_seed) {
        cat(sprintf(
          "  -> Running seed %d of %d: seed = %d\n",
          s_idx,
          n_seed,
          seed
        ))
      }
      
      env <- generate_piecewise_env(
        horizon = scenario$horizon,
        breakpoints = scenario$breakpoints,
        means = scenario$means,
        sds = scenario$sds,
        seed = seed,
        arm_names = scenario$arm_names
      )
      
      oracle <- compute_dynamic_oracle(
        env = env,
        rho = rho,
        switching_cost = switching_cost
      )
      
      runs <- list(
        `UCB1` = run_ucb1_env(
          env = env,
          switching_cost = switching_cost,
          rho = rho,
          oracle = oracle
        ),
        
        `SW-UCB` = run_swucb_env(
          env = env,
          switching_cost = switching_cost,
          rho = rho,
          oracle = oracle
        ),
        
        `D-UCB` = run_ducb_env(
          env = env,
          switching_cost = switching_cost,
          rho = rho,
          oracle = oracle
        ),
        
        `CUSUM-UCB` = run_cd_ucb_env(
          env = env,
          alpha = cd_alpha,
          switching_cost = switching_cost,
          M = cd_M,
          epsilon = cd_epsilon,
          h_thresh = cd_h,
          rho = rho,
          oracle = oracle
        ),
        
        `RS-SC-CUSUM-UCB` = run_rs_sc_cusum_ucb_env(
          env = env,
          alpha = cd_alpha,
          rho = rho,
          switching_cost = switching_cost,
          barrier = rs_barrier,
          M = cd_M,
          epsilon = cd_epsilon,
          h_thresh = cd_h,
          oracle = oracle
        )
      )
      
      for (alg in names(runs)) {
        run_df <- runs[[alg]]
        
        all_summary[[summary_idx]] <- summarise_sim_run(
          run_df = run_df,
          algorithm_name = alg,
          scenario_name = scenario$name,
          seed = seed,
          breakpoints = scenario$breakpoints
        )
        summary_idx <- summary_idx + 1L
        
        path_acc <- update_path_accumulator(
          acc = path_acc,
          run_df = run_df,
          alg = alg
        )
        
        if (seed %in% keep_path_seeds) {
          chosen_arm_paths[[chosen_idx]] <- extract_chosen_arm_path(
            run_df = run_df,
            alg = alg,
            seed = seed,
            scenario_name = scenario$name
          )
          chosen_idx <- chosen_idx + 1L
          
          if (save_compact_paths) {
            compact_paths[[compact_idx]] <- extract_compact_path(
              run_df = run_df,
              alg = alg,
              seed = seed,
              scenario_name = scenario$name
            )
            compact_idx <- compact_idx + 1L
          }
        }
      }
      
      rm(runs, env, oracle)
      
      if (!is.null(gc_every) && gc_every > 0 && s_idx %% gc_every == 0) {
        gc(verbose = FALSE)
      }
    }
    
    df_summary <- rbind_fill(all_summary)
    agg <- summarise_by_algorithm(df_summary)
    
    cat(sprintf(
      "\n--- LEADERBOARD: %s, average over %d seeds ---\n",
      scenario$name,
      length(seeds)
    ))
    print(agg)
    
    write.csv(
      df_summary,
      file = file.path(tables_dir, "summary_by_seed.csv"),
      row.names = FALSE
    )
    
    write.csv(
      agg,
      file = file.path(tables_dir, "leaderboard.csv"),
      row.names = FALSE
    )
    
    mean_paths <- list(
      mv_value_df = accumulator_to_plot_df(
        path_acc[["cum_realised_mv_utility_net"]],
        n_seeds = length(seeds)
      ),
      mv_regret_df = accumulator_to_plot_df(
        path_acc[["cum_regret_mv_sc"]],
        n_seeds = length(seeds)
      ),
      avg_regret_df = accumulator_to_plot_df(
        path_acc[["avg_regret_mv_sc"]],
        n_seeds = length(seeds)
      ),
      log_wealth_df = accumulator_to_plot_df(
        path_acc[["log_wealth"]],
        n_seeds = length(seeds)
      ),
      cost_df = accumulator_to_plot_df(
        path_acc[["cum_cost_paid"]],
        n_seeds = length(seeds)
      )
    )
    
    write.csv(
      mean_paths$mv_value_df,
      file = file.path(tables_dir, "mean_path_cum_mv_utility_net.csv"),
      row.names = FALSE
    )
    
    write.csv(
      mean_paths$mv_regret_df,
      file = file.path(tables_dir, "mean_path_cum_regret_mv_sc.csv"),
      row.names = FALSE
    )
    
    write.csv(
      mean_paths$avg_regret_df,
      file = file.path(tables_dir, "mean_path_avg_regret_mv_sc.csv"),
      row.names = FALSE
    )
    
    write.csv(
      mean_paths$log_wealth_df,
      file = file.path(tables_dir, "mean_path_log_wealth.csv"),
      row.names = FALSE
    )
    
    write.csv(
      mean_paths$cost_df,
      file = file.path(tables_dir, "mean_path_cum_cost.csv"),
      row.names = FALSE
    )
    
    if (save_compact_paths && length(compact_paths) > 0) {
      df_compact_paths <- rbind_fill(compact_paths)
      
      write.csv(
        df_compact_paths,
        file = file.path(tables_dir, "compact_paths_selected_seeds.csv"),
        row.names = FALSE
      )
    }
    
    cat("  -> Generating plots...\n")
    
    make_line_plot(
      plot_df = mean_paths$mv_value_df,
      breakpoints = scenario$breakpoints,
      ylab = "Cumulative MV utility, net of switching cost",
      outfile = file.path(figures_dir, "cum_mv_utility_net.png"),
      legend_position = "topleft"
    )
    
    make_line_plot(
      plot_df = mean_paths$mv_regret_df,
      breakpoints = scenario$breakpoints,
      ylab = "Cumulative regret",
      outfile = file.path(figures_dir, "cum_regret_mv_sc.png"),
      legend_position = "topleft"
    )
    
    make_line_plot(
      plot_df = mean_paths$avg_regret_df,
      breakpoints = scenario$breakpoints,
      ylab = "Mean regret",
      outfile = file.path(figures_dir, "avg_regret_mv_sc.png"),
      legend_position = "topright"
    )
    
    make_line_plot(
      plot_df = mean_paths$log_wealth_df,
      breakpoints = scenario$breakpoints,
      ylab = "Log wealth",
      outfile = file.path(figures_dir, "log_wealth.png"),
      legend_position = "topleft"
    )
    
    make_line_plot(
      plot_df = mean_paths$cost_df,
      breakpoints = scenario$breakpoints,
      ylab = "Cumulative cost",
      outfile = file.path(figures_dir, "cum_cost.png"),
      legend_position = "topleft"
    )
    
    df_chosen_paths <- rbind_fill(chosen_arm_paths)
    
    if (nrow(df_chosen_paths) > 0) {
      make_chosen_arm_plot(
        paths = df_chosen_paths,
        breakpoints = scenario$breakpoints,
        outfile = file.path(
          figures_dir,
          paste0("chosen_arm_seed", keep_path_seeds[1], ".png")
        ),
        seed = keep_path_seeds[1]
      )
      
      write.csv(
        df_chosen_paths,
        file = file.path(tables_dir, "chosen_arm_selected_seeds.csv"),
        row.names = FALSE
      )
    }
    
    all_results[[scen_key]] <- list(
      summary_by_seed = df_summary,
      leaderboard = agg,
      mean_paths = mean_paths,
      chosen_arm_paths = df_chosen_paths
    )
    
    rm(
      all_summary,
      df_summary,
      agg,
      path_acc,
      chosen_arm_paths,
      compact_paths,
      mean_paths,
      df_chosen_paths
    )
    gc(verbose = FALSE)
  }
  
  cat("\nSimulation and plotting complete.\n")
  invisible(all_results)
}

# 8) Run
results_test_10000 <- run_full_simulation(
  seeds = 1:10000,
  switching_cost = 0.005,
  rho = 1,
  rs_barrier = 0,
  cd_alpha = 0.015,
  cd_M = 40,
  cd_epsilon = 0.004,
  cd_h = 0.12,
  output_dir = "outputs_test_final1",
  keep_path_seeds = c(1),
  save_compact_paths = FALSE
)

# 10) Robustness and Sensitivity Checks
# 10.1 Theory-aligned 
compute_piecewise_oracle <- function(env, rho, switching_cost = 0) {
  u_mat <- compute_mv_utility_scores(env, rho)
  
  Tt <- env$horizon
  oracle_id <- max.col(u_mat, ties.method = "first")
  oracle_switch <- c(0L, as.integer(diff(oracle_id) != 0))
  
  oracle_u <- u_mat[cbind(seq_len(Tt), oracle_id)]
  oracle_inst_net <- oracle_u - switching_cost * oracle_switch
  
  list(
    oracle_id = oracle_id,
    oracle_name = env$arm_names[oracle_id],
    oracle_switch = oracle_switch,
    oracle_u = oracle_u,
    oracle_inst_net = oracle_inst_net,
    oracle_cum_net = cumsum(oracle_inst_net),
    total_switches = sum(oracle_switch)
  )
}

compute_path_net_utility <- function(env, arm_id, rho, switching_cost) {
  u_mat <- compute_mv_utility_scores(env, rho)
  Tt <- env$horizon
  
  arm_id <- as.integer(arm_id)
  switches <- c(0L, as.integer(diff(arm_id) != 0))
  
  inst_net <- u_mat[cbind(seq_len(Tt), arm_id)] - switching_cost * switches
  sum(inst_net)
}

compute_theory_constants <- function(env, rho, switching_cost, breakpoints) {
  u_mat <- compute_mv_utility_scores(env, rho)
  regimes <- sort(unique(env$regime))
  
  gap_rows <- lapply(regimes, function(j) {
    idx <- which(env$regime == j)[1]
    u_j <- u_mat[idx, ]
    
    best_id <- which.max(u_j)
    gaps <- u_j[best_id] - u_j
    
    sub_gaps <- gaps[-best_id]
    
    data.frame(
      regime = j,
      best_arm_id = best_id,
      best_arm = env$arm_names[best_id],
      min_gap = min(sub_gaps),
      max_gap = max(sub_gaps),
      min_effective_gap = min(sub_gaps) - switching_cost,
      stringsAsFactors = FALSE
    )
  })
  
  gap_table <- do.call(rbind, gap_rows)
  
  data.frame(
    upsilon_T = length(breakpoints),
    min_mv_gap = min(gap_table$min_gap),
    max_mv_gap = max(gap_table$max_gap),
    min_effective_gap = min(gap_table$min_effective_gap),
    effective_gap_condition = as.integer(min(gap_table$min_effective_gap) > 0),
    c_upsilon_bound = switching_cost * length(breakpoints),
    stringsAsFactors = FALSE
  )
}

compute_run_theory_diagnostics <- function(env,
                                           chosen_arm_id,
                                           rho,
                                           switching_cost,
                                           breakpoints,
                                           dynamic_oracle = NULL) {
  if (is.null(dynamic_oracle)) {
    dynamic_oracle <- compute_dynamic_oracle(
      env = env,
      rho = rho,
      switching_cost = switching_cost
    )
  }
  
  ps_oracle <- compute_piecewise_oracle(
    env = env,
    rho = rho,
    switching_cost = switching_cost
  )
  
  u_mat <- compute_mv_utility_scores(env, rho)
  Tt <- env$horizon
  
  chosen_arm_id <- as.integer(chosen_arm_id)
  
  policy_net <- compute_path_net_utility(
    env = env,
    arm_id = chosen_arm_id,
    rho = rho,
    switching_cost = switching_cost
  )
  
  ps_net <- tail(ps_oracle$oracle_cum_net, 1)
  dyn_net <- tail(dynamic_oracle$oracle_cum_net, 1)
  
  pseudo_regret_ps <- ps_net - policy_net
  regret_dyn <- dyn_net - policy_net
  dyn_minus_ps <- dyn_net - ps_net
  
  ps_id <- ps_oracle$oracle_id
  mismatch <- as.integer(chosen_arm_id != ps_id)
  
  delta_t <- u_mat[cbind(seq_len(Tt), ps_id)] -
    u_mat[cbind(seq_len(Tt), chosen_arm_id)]
  
  reduced_bound_ps <- sum((delta_t + 2 * switching_cost) * mismatch)
  
  data.frame(
    final_pseudo_regret_ps = pseudo_regret_ps,
    final_dynamic_regret_check = regret_dyn,
    reduced_bound_ps = reduced_bound_ps,
    reduced_bound_slack_ps = reduced_bound_ps - pseudo_regret_ps,
    reduced_bound_holds = as.integer(reduced_bound_ps + 1e-10 >= pseudo_regret_ps),
    dyn_minus_ps_oracle_net = dyn_minus_ps,
    dyn_ps_bound_slack = switching_cost * length(breakpoints) - dyn_minus_ps,
    dyn_ps_bound_holds = as.integer(
      dyn_minus_ps <= switching_cost * length(breakpoints) + 1e-10
    ),
    stringsAsFactors = FALSE
  )
}

# 10.2 Policy suite 

run_policy_suite <- function(env,
                             switching_cost,
                             rho,
                             rs_barrier = 0,
                             oracle = NULL) {
  if (is.null(oracle)) {
    oracle <- compute_dynamic_oracle(
      env = env,
      rho = rho,
      switching_cost = switching_cost
    )
  }
  
  list(
    `UCB1` = run_ucb1_env(
      env = env,
      switching_cost = switching_cost,
      rho = rho,
      oracle = oracle
    ),
    
    `SW-UCB` = run_swucb_env(
      env = env,
      switching_cost = switching_cost,
      rho = rho,
      oracle = oracle
    ),
    
    `D-UCB` = run_ducb_env(
      env = env,
      switching_cost = switching_cost,
      rho = rho,
      oracle = oracle
    ),
    
    `CUSUM-UCB` = run_cd_ucb_env(
      env = env,
      switching_cost = switching_cost,
      rho = rho,
      oracle = oracle
    ),
    
    `RS-SC-CUSUM-UCB` = run_rs_sc_cusum_ucb_env(
      env = env,
      switching_cost = switching_cost,
      rho = rho,
      barrier = rs_barrier,
      oracle = oracle
    )
  )
}

# 10.3 Sensitivity configuration generator

make_sensitivity_configs <- function(rho_grid = c(0, 0.25, 0.50, 1.25, 1.50, 1.75, 2.00, 3.00),
                                     cost_grid = c(0, 0.001, 0.003, 0.005, 0.007, 0.010, 0.015),
                                     baseline_rho = 1,
                                     baseline_cost = 0.005,
                                     include_two_way = FALSE) {
  risk_configs <- data.frame(
    experiment = "risk_tolerance_sensitivity",
    rho = rho_grid,
    switching_cost = baseline_cost,
    stringsAsFactors = FALSE
  )
  
  cost_configs <- data.frame(
    experiment = "switching_cost_sensitivity",
    rho = baseline_rho,
    switching_cost = cost_grid,
    stringsAsFactors = FALSE
  )
  
  configs <- rbind(risk_configs, cost_configs)
  
  if (include_two_way) {
    two_way <- expand.grid(
      rho = rho_grid,
      switching_cost = cost_grid
    )
    
    two_way$experiment <- "two_way_rho_cost_robustness"
    two_way <- two_way[, c("experiment", "rho", "switching_cost")]
    
    configs <- rbind(configs, two_way)
  }
  
  configs <- unique(configs)
  rownames(configs) <- NULL
  configs$config_id <- seq_len(nrow(configs))
  
  configs
}

# 10.4 Aggregate sensitivity results

summarise_sensitivity_results <- function(df_summary) {
  metric_cols <- c(
    "final_cum_mv_utility_net",
    "final_cum_regret_mv_sc",
    "final_avg_regret_mv_sc",
    "final_pseudo_regret_ps",
    "final_dynamic_regret_check",
    "reduced_bound_ps",
    "reduced_bound_slack_ps",
    "reduced_bound_holds",
    "dyn_minus_ps_oracle_net",
    "dyn_ps_bound_slack",
    "dyn_ps_bound_holds",
    "min_mv_gap",
    "max_mv_gap",
    "min_effective_gap",
    "effective_gap_condition",
    "c_upsilon_bound",
    "final_cum_regret_mean",
    "terminal_log_wealth",
    "terminal_wealth_index",
    "sharpe_net",
    "total_switches",
    "total_cost_paid",
    "oracle_share_dynamic",
    "oracle_share_pointwise_mv",
    "total_alarms",
    "false_alarms",
    "false_alarm_rate",
    "detected_breaks",
    "mean_detection_delay"
  )
  
  metric_cols <- intersect(metric_cols, names(df_summary))
  
  group_vars <- c(
    "experiment",
    "scenario",
    "rho",
    "switching_cost",
    "algorithm"
  )
  
  split_key <- do.call(
    interaction,
    c(df_summary[group_vars], list(drop = TRUE, lex.order = TRUE))
  )
  
  groups <- split(df_summary, split_key)
  
  out <- lapply(groups, function(sub) {
    row <- sub[1, group_vars, drop = FALSE]
    
    for (mc in metric_cols) {
      x <- sub[[mc]]
      x <- x[is.finite(x)]
      
      row[[paste0("mean_", mc)]] <- if (length(x) == 0) NA_real_ else mean(x)
      row[[paste0("sd_", mc)]] <- if (length(x) <= 1) NA_real_ else sd(x)
      row[[paste0("se_", mc)]] <- if (length(x) <= 1) NA_real_ else sd(x) / sqrt(length(x))
    }
    
    row$n_seeds <- length(unique(sub$seed))
    row
  })
  
  agg <- do.call(rbind, out)
  rownames(agg) <- NULL
  
  agg <- agg[order(
    agg$experiment,
    agg$scenario,
    agg$rho,
    agg$switching_cost,
    match(agg$algorithm, POLICY_ORDER)
  ), ]
  
  rownames(agg) <- NULL
  agg
}

# 10.5 Sensitivity line plots

get_policy_colour <- function(alg) {
  cols <- POLICY_COLS
  
  if (is.null(names(cols)) || any(names(cols) == "")) {
    names(cols) <- POLICY_ORDER[seq_along(cols)]
  }
  
  if (alg %in% names(cols)) cols[[alg]] else "grey40"
}

make_sensitivity_line_plot <- function(agg_df,
                                       experiment_name,
                                       scenario_name,
                                       x_var,
                                       metric,
                                       ylab,
                                       outfile,
                                       legend_position = "topleft") {
  dir.create(dirname(outfile), recursive = TRUE, showWarnings = FALSE)
  
  sub <- agg_df[
    agg_df$experiment == experiment_name &
      agg_df$scenario == scenario_name,
    ,
    drop = FALSE
  ]
  
  if (nrow(sub) == 0) {
    warning(sprintf("No data for %s / %s", experiment_name, scenario_name))
    return(invisible(NULL))
  }
  
  y_var <- paste0("mean_", metric)
  
  if (!y_var %in% names(sub)) {
    warning(sprintf("Metric not found in aggregated data: %s", y_var))
    return(invisible(NULL))
  }
  
  sub <- sub[is.finite(sub[[x_var]]) & is.finite(sub[[y_var]]), , drop = FALSE]
  
  if (nrow(sub) == 0) {
    warning(sprintf("No finite plotting data for %s", outfile))
    return(invisible(NULL))
  }
  
  algs <- intersect(POLICY_ORDER, unique(sub$algorithm))
  extra_algs <- setdiff(unique(sub$algorithm), algs)
  algs <- c(algs, extra_algs)
  
  xlab <- switch(
    x_var,
    rho = expression("Risk-tolerance parameter " * rho),
    switching_cost = "Switching cost",
    x_var
  )
  
  png(outfile, width = 1200, height = 750, res = 130)
  on.exit(dev.off(), add = TRUE)
  
  old_par <- par(no.readonly = TRUE)
  on.exit(par(old_par), add = TRUE)
  
  par(
    mar = c(4.8, 5.2, 1.0, 1.2),
    mgp = c(2.9, 0.8, 0),
    las = 1
  )
  
  plot(
    NA,
    xlim = range(sub[[x_var]], na.rm = TRUE),
    ylim = add_y_padding(sub[[y_var]]),
    xlab = xlab,
    ylab = ylab,
    main = "",
    cex.lab = 1.15,
    cex.axis = 1.0
  )
  
  grid(col = "grey88", lty = "dotted")
  
  for (alg in algs) {
    df <- sub[sub$algorithm == alg, , drop = FALSE]
    df <- df[order(df[[x_var]]), ]
    
    lines(
      df[[x_var]],
      df[[y_var]],
      col = get_policy_colour(alg),
      lwd = 2.2,
      type = "b",
      pch = 16
    )
  }
  
  legend(
    legend_position,
    legend = algs,
    col = vapply(algs, get_policy_colour, character(1)),
    lwd = 2.2,
    pch = 16,
    bty = "n",
    cex = 0.95
  )
  
  invisible(NULL)
}

# 10.6 Main sensitivity engine

run_sensitivity_simulation <- function(seeds = 1:1000,
                                       rho_grid = c(0, 0.25, 0.50, 1.25, 1.50, 1.75, 2.00, 3.00),
                                       cost_grid = c(0, 0.001, 0.003, 0.005, 0.007, 0.010, 0.015),
                                       baseline_rho = 1,
                                       baseline_cost = 0.005,
                                       rs_barrier = 0,
                                       include_two_way = FALSE,
                                       output_dir = "outputs_sensitivity",
                                       gc_every = 25) {
  scenarios <- get_sim_scenarios()
  
  configs <- make_sensitivity_configs(
    rho_grid = rho_grid,
    cost_grid = cost_grid,
    baseline_rho = baseline_rho,
    baseline_cost = baseline_cost,
    include_two_way = include_two_way
  )
  
  dir.create(output_dir, recursive = TRUE, showWarnings = FALSE)
  
  tables_dir <- file.path(output_dir, "tables")
  figures_dir <- file.path(output_dir, "figures")
  
  dir.create(tables_dir, recursive = TRUE, showWarnings = FALSE)
  dir.create(figures_dir, recursive = TRUE, showWarnings = FALSE)
  
  all_summary <- list()
  idx <- 1L
  
  cat("\n======================================================\n")
  cat("STARTING ROBUSTNESS AND SENSITIVITY CHECKS\n")
  cat("======================================================\n")
  cat(sprintf("Number of configurations: %d\n", nrow(configs)))
  cat(sprintf("Number of seeds per configuration: %d\n", length(seeds)))
  cat(sprintf("RS implementation barrier b: %.6f\n", rs_barrier))
  
  for (cfg_i in seq_len(nrow(configs))) {
    cfg <- configs[cfg_i, ]
    
    cat("\n------------------------------------------------------\n")
    cat(sprintf(
      "Configuration %d of %d: %s | rho = %.4f | c = %.4f\n",
      cfg_i,
      nrow(configs),
      cfg$experiment,
      cfg$rho,
      cfg$switching_cost
    ))
    cat("------------------------------------------------------\n")
    
    for (scen_key in names(scenarios)) {
      scenario <- scenarios[[scen_key]]
      
      cat(sprintf("  Scenario: %s\n", scenario$name))
      
      env_template <- generate_piecewise_env(
        horizon = scenario$horizon,
        breakpoints = scenario$breakpoints,
        means = scenario$means,
        sds = scenario$sds,
        seed = seeds[1],
        arm_names = scenario$arm_names
      )
      
      theory_constants <- compute_theory_constants(
        env = env_template,
        rho = cfg$rho,
        switching_cost = cfg$switching_cost,
        breakpoints = scenario$breakpoints
      )
      
      if (theory_constants$effective_gap_condition == 0) {
        cat(sprintf(
          "    Warning: positive effective-gap condition fails. min(Delta - c) = %.6f\n",
          theory_constants$min_effective_gap
        ))
      }
      
      rm(env_template)
      
      for (s_idx in seq_along(seeds)) {
        seed <- seeds[s_idx]
        
        if (s_idx %% 25 == 1 || s_idx == length(seeds)) {
          cat(sprintf(
            "    -> Seed %d of %d: seed = %d\n",
            s_idx,
            length(seeds),
            seed
          ))
        }
        
        env <- generate_piecewise_env(
          horizon = scenario$horizon,
          breakpoints = scenario$breakpoints,
          means = scenario$means,
          sds = scenario$sds,
          seed = seed,
          arm_names = scenario$arm_names
        )
        
        oracle <- compute_dynamic_oracle(
          env = env,
          rho = cfg$rho,
          switching_cost = cfg$switching_cost
        )
        
        runs <- run_policy_suite(
          env = env,
          switching_cost = cfg$switching_cost,
          rho = cfg$rho,
          rs_barrier = rs_barrier,
          oracle = oracle
        )
        
        for (alg in names(runs)) {
          row <- summarise_sim_run(
            run_df = runs[[alg]],
            algorithm_name = alg,
            scenario_name = scenario$name,
            seed = seed,
            breakpoints = scenario$breakpoints
          )
          
          theory_diag <- compute_run_theory_diagnostics(
            env = env,
            chosen_arm_id = runs[[alg]]$chosen_arm_id,
            rho = cfg$rho,
            switching_cost = cfg$switching_cost,
            breakpoints = scenario$breakpoints,
            dynamic_oracle = oracle
          )
          
          row$experiment <- cfg$experiment
          row$rho <- cfg$rho
          row$switching_cost <- cfg$switching_cost
          row$config_id <- cfg$config_id
          
          row <- cbind(
            row,
            theory_constants,
            theory_diag
          )
          
          all_summary[[idx]] <- row
          idx <- idx + 1L
        }
        
        rm(env, oracle, runs)
        
        if (!is.null(gc_every) && gc_every > 0 && s_idx %% gc_every == 0) {
          gc(verbose = FALSE)
        }
      }
    }
  }
  
  df_summary <- rbind_fill(all_summary)
  
  front_cols <- c(
    "experiment",
    "config_id",
    "scenario",
    "algorithm",
    "seed",
    "rho",
    "switching_cost"
  )
  
  df_summary <- df_summary[, c(
    front_cols,
    setdiff(names(df_summary), front_cols)
  )]
  
  agg <- summarise_sensitivity_results(df_summary)
  
  write.csv(
    configs,
    file = file.path(tables_dir, "sensitivity_configurations.csv"),
    row.names = FALSE
  )
  
  write.csv(
    df_summary,
    file = file.path(tables_dir, "sensitivity_by_seed.csv"),
    row.names = FALSE
  )
  
  write.csv(
    agg,
    file = file.path(tables_dir, "sensitivity_aggregated.csv"),
    row.names = FALSE
  )
  
  diagnostic_cols <- c(
    "experiment",
    "scenario",
    "rho",
    "switching_cost",
    "algorithm",
    "n_seeds",
    "mean_min_mv_gap",
    "mean_min_effective_gap",
    "mean_effective_gap_condition",
    "mean_final_cum_mv_utility_net",
    "mean_final_cum_regret_mv_sc",
    "mean_final_pseudo_regret_ps",
    "mean_reduced_bound_ps",
    "mean_reduced_bound_slack_ps",
    "mean_reduced_bound_holds",
    "mean_dyn_minus_ps_oracle_net",
    "mean_dyn_ps_bound_slack",
    "mean_dyn_ps_bound_holds",
    "mean_total_switches",
    "mean_total_cost_paid",
    "mean_total_alarms",
    "mean_false_alarms",
    "mean_false_alarm_rate",
    "mean_detected_breaks",
    "mean_mean_detection_delay",
    "mean_oracle_share_dynamic",
    "mean_oracle_share_pointwise_mv"
  )
  
  diagnostic_cols <- intersect(diagnostic_cols, names(agg))
  diagnostic_table <- agg[, diagnostic_cols, drop = FALSE]
  
  write.csv(
    diagnostic_table,
    file = file.path(tables_dir, "diagnostic_theory_detection_switching_table.csv"),
    row.names = FALSE
  )
  
# Figures: sensitivity to rho
  for (scenario_name in unique(agg$scenario)) {
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "risk_tolerance_sensitivity",
      scenario_name = scenario_name,
      x_var = "rho",
      metric = "final_cum_mv_utility_net",
      ylab = "Final cumulative MV net value",
      outfile = file.path(
        figures_dir,
        paste0("risk_sensitivity_mv_value_", scenario_name, ".png")
      ),
      legend_position = "topleft"
    )
    
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "risk_tolerance_sensitivity",
      scenario_name = scenario_name,
      x_var = "rho",
      metric = "final_cum_regret_mv_sc",
      ylab = "Final cumulative dynamic-oracle regret",
      outfile = file.path(
        figures_dir,
        paste0("risk_sensitivity_dynamic_regret_", scenario_name, ".png")
      ),
      legend_position = "topleft"
    )
    
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "risk_tolerance_sensitivity",
      scenario_name = scenario_name,
      x_var = "rho",
      metric = "final_pseudo_regret_ps",
      ylab = "Final pseudo-regret against piecewise oracle",
      outfile = file.path(
        figures_dir,
        paste0("risk_sensitivity_ps_pseudo_regret_", scenario_name, ".png")
      ),
      legend_position = "topleft"
    )
    
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "risk_tolerance_sensitivity",
      scenario_name = scenario_name,
      x_var = "rho",
      metric = "total_switches",
      ylab = "Total switches",
      outfile = file.path(
        figures_dir,
        paste0("risk_sensitivity_switches_", scenario_name, ".png")
      ),
      legend_position = "topleft"
    )
  }
  

# Figures: sensitivity to switching cost

  for (scenario_name in unique(agg$scenario)) {
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "switching_cost_sensitivity",
      scenario_name = scenario_name,
      x_var = "switching_cost",
      metric = "final_cum_mv_utility_net",
      ylab = "Final cumulative MV net value",
      outfile = file.path(
        figures_dir,
        paste0("cost_sensitivity_mv_value_", scenario_name, ".png")
      ),
      legend_position = "topleft"
    )
    
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "switching_cost_sensitivity",
      scenario_name = scenario_name,
      x_var = "switching_cost",
      metric = "final_cum_regret_mv_sc",
      ylab = "Final cumulative dynamic-oracle regret",
      outfile = file.path(
        figures_dir,
        paste0("cost_sensitivity_dynamic_regret_", scenario_name, ".png")
      ),
      legend_position = "topleft"
    )
    
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "switching_cost_sensitivity",
      scenario_name = scenario_name,
      x_var = "switching_cost",
      metric = "final_pseudo_regret_ps",
      ylab = "Final pseudo-regret against piecewise oracle",
      outfile = file.path(
        figures_dir,
        paste0("cost_sensitivity_ps_pseudo_regret_", scenario_name, ".png")
      ),
      legend_position = "topleft"
    )
    
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "switching_cost_sensitivity",
      scenario_name = scenario_name,
      x_var = "switching_cost",
      metric = "total_switches",
      ylab = "Total switches",
      outfile = file.path(
        figures_dir,
        paste0("cost_sensitivity_switches_", scenario_name, ".png")
      ),
      legend_position = "topright"
    )
    
    make_sensitivity_line_plot(
      agg_df = agg,
      experiment_name = "switching_cost_sensitivity",
      scenario_name = scenario_name,
      x_var = "switching_cost",
      metric = "total_cost_paid",
      ylab = "Total switching cost paid",
      outfile = file.path(
        figures_dir,
        paste0("cost_sensitivity_total_cost_", scenario_name, ".png")
      ),
      legend_position = "topleft"
    )
  }
  
  cat("\nSensitivity checks complete.\n")
  cat(sprintf("Tables saved to: %s\n", tables_dir))
  cat(sprintf("Figures saved to: %s\n", figures_dir))
  
  invisible(list(
    configs = configs,
    summary_by_seed = df_summary,
    aggregated = agg,
    diagnostic_table = diagnostic_table
  ))
}

# 11) Run Robustness and Sensitivity Checks

sensitivity_results <- run_sensitivity_simulation(
  seeds = 1:1000,
  
  rho_grid = c(0, 0.25, 0.50, 1.25, 1.50, 1.75, 2.00, 3.00),
  cost_grid = c(0, 0.001, 0.003, 0.005, 0.007, 0.010, 0.015),
  
  baseline_rho = 1,
  baseline_cost = 0.005,
  
  # Set to zero for clean sensitivity analysis of c.
  rs_barrier = 0,
  
  include_two_way = FALSE,
  
  output_dir = "outputs_sensitivity",
  gc_every = 25
)
