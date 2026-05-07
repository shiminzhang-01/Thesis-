rm(list = ls())

# 0) Packages
required_pkgs <- c("quantmod", "xts", "zoo", "PerformanceAnalytics")
for (p in required_pkgs) {
  if (!requireNamespace(p, quietly = TRUE)) install.packages(p)
}

library(quantmod)
library(xts)
library(zoo)
library(PerformanceAnalytics)

# 1) Universe and configuration
ETF_TICKERS <- c("SPY", "EFA", "TLT", "IEF", "TIP", "DBC", "VNQ", "SHY")

ALGORITHM_ORDER <- c(
  "UCB1",
  "SW-UCB",
  "D-UCB",
  "CUSUM-UCB",
  "RS-SC-CUSUM-UCB"
)

POLICY_COLS <- c("#E69F00", "#009E73", "#56B4E9", "#D55E00", "#cc79A7")

cfg <- list(
  from = "2006-01-01",
  to = "2026-04-12",
  output_dir = "us_multiasset_weighted_no_iau_outputs",

  initial_wealth = 1,
  warmup_weeks = 52,

  weekly_cost = 0.0005,
  
  rs_rho = 1.25,

  eval_var_window = 52,
  eval_var_cap = 0.0015,

  portfolio_seed = 777,
  n_random_portfolios = 120,
  max_weight = 0.45,
  min_active_weight = 0.03,

  # SW-UCB
  sw_alpha = 0.10,
  sw_tau = 52,

  # D-UCB
  du_alpha = 0.10,
  du_gamma = 0.997,

  # CUSUM-UCB benchmark
  cd_alpha = 0.003,
  cd_bonus_scale = 0.60,
  cd_M = 52,
  cd_epsilon = 0.0025,
  cd_h = 0.16,
  cd_post_alarm_pulls = 6,

  # Proposed RS-SC-CUSUM-UCB
  rs_alpha = 0.002,
  rs_barrier = 0.00025,
  rs_bonus_scale = 0.35,
  rs_M_mean = 52,
  rs_M_var = 52,
  rs_epsilon_mean = 0.0015,
  rs_epsilon_var = 0.00025,
  rs_h_mean = 0.12,
  rs_h_var = 0.08,
  rs_post_alarm_pulls = 6
)

# 2) General helpers

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

max_drawdown_simple <- function(wealth) {
  wealth <- as.numeric(wealth)
  wealth <- wealth[is.finite(wealth)]
  if (length(wealth) == 0) return(NA_real_)

  running_max <- cummax(wealth)
  dd <- wealth / running_max - 1
  min(dd, na.rm = TRUE)
}

annualised_return_from_wealth <- function(wealth,
                                          initial_wealth = 1,
                                          periods_per_year = 52) {
  wealth <- as.numeric(wealth)
  n <- length(wealth)

  if (n <= 1) return(NA_real_)

  final <- tail(wealth, 1)
  if (!is.finite(final) || final <= 0 || initial_wealth <= 0) return(NA_real_)

  (final / initial_wealth)^(periods_per_year / n) - 1
}

annualised_vol <- function(net_returns, periods_per_year = 52) {
  sd(as.numeric(net_returns), na.rm = TRUE) * sqrt(periods_per_year)
}

sharpe_simple <- function(net_returns, rf = 0, periods_per_year = 52) {
  mu <- mean(as.numeric(net_returns), na.rm = TRUE) * periods_per_year
  vol <- annualised_vol(net_returns, periods_per_year)

  if (is.na(vol) || vol == 0) return(NA_real_)

  (mu - rf) / vol
}

ordered_algorithms <- function(algs) {
  c(ALGORITHM_ORDER[ALGORITHM_ORDER %in% algs], setdiff(algs, ALGORITHM_ORDER))
}

policy_colours <- function(algs) {
  algs <- ordered_algorithms(algs)
  cols <- POLICY_COLS[seq_along(algs)]
  names(cols) <- algs
  cols
}

# 3) Data download and cleaning

download_adjusted_prices <- function(tickers, from, to) {
  price_list <- lapply(tickers, function(sym) {
    x <- getSymbols(
      Symbols = sym,
      src = "yahoo",
      from = from,
      to = to,
      auto.assign = FALSE
    )

    px <- Ad(x)
    colnames(px) <- sym
    px
  })

  prices_daily <- do.call(merge, price_list)
  prices_daily <- prices_daily[complete.cases(prices_daily), ]
  prices_daily
}

build_weekly_prices <- function(prices_daily) {
  ep <- endpoints(prices_daily, on = "weeks")
  ep <- ep[ep > 0]
  prices_weekly <- prices_daily[ep, ]
  prices_weekly
}

build_weekly_returns <- function(prices_weekly) {
  ret <- Return.calculate(prices_weekly, method = "discrete")
  ret <- ret[-1, ]
  ret <- na.omit(ret)
  ret
}

build_pretrade_variance <- function(rets_xts, window = 52) {
  R <- coredata(rets_xts)
  h <- nrow(R)
  k <- ncol(R)

  out <- matrix(0, nrow = h, ncol = k)
  colnames(out) <- colnames(R)

  for (i in seq_len(k)) {
    for (t in seq_len(h)) {
      if (t <= 2) {
        out[t, i] <- 0
      } else {
        start <- max(1, t - window)
        hist <- R[start:(t - 1), i]
        hist <- hist[is.finite(hist)]
        out[t, i] <- if (length(hist) <= 1) 0 else var(hist)
      }
    }
  }

  xts(out, order.by = index(rets_xts))
}

# 4) Portfolio-arm construction

normalise_weight <- function(w, tickers) {
  out <- setNames(rep(0, length(tickers)), tickers)
  out[names(w)] <- as.numeric(w)

  s <- sum(out)
  if (s <= 0) stop("Portfolio weights must sum to a positive value.")

  out / s
}

random_portfolio_library <- function(tickers,
                                     n_portfolios = 120,
                                     max_weight = 0.45,
                                     min_active_weight = 0.03,
                                     seed = 777) {
  set.seed(seed)

  K <- length(tickers)
  W <- matrix(NA_real_, nrow = n_portfolios, ncol = K)
  colnames(W) <- tickers

  count <- 0
  attempts <- 0

  while (count < n_portfolios && attempts < 100000) {
    attempts <- attempts + 1

    x <- rexp(K, rate = 1)
    w <- x / sum(x)

    if (max(w) <= max_weight && sum(w > min_active_weight) >= 4) {
      count <- count + 1
      W[count, ] <- w
    }
  }

  if (count < n_portfolios) {
    warning("Could not generate the requested number of random portfolios.")
    W <- W[seq_len(count), , drop = FALSE]
  }

  rownames(W) <- paste0("RandomPortfolio_", seq_len(nrow(W)))
  W
}

make_portfolio_library <- function(tickers,
                                   n_random_portfolios = 120,
                                   max_weight = 0.45,
                                   min_active_weight = 0.03,
                                   seed = 777) {
  K <- length(tickers)

  equal_weight <- setNames(rep(1 / K, K), tickers)

  manual <- rbind(
    EqualWeight = equal_weight,

    Balanced_60_40 = normalise_weight(c(
      SPY = 0.30,
      EFA = 0.15,
      VNQ = 0.05,
      TLT = 0.20,
      IEF = 0.15,
      TIP = 0.05,
      SHY = 0.10
    ), tickers),

    Defensive_Bond = normalise_weight(c(
      TLT = 0.30,
      IEF = 0.25,
      SHY = 0.25,
      TIP = 0.10,
      SPY = 0.10
    ), tickers),

    Growth_Diversified = normalise_weight(c(
      SPY = 0.35,
      EFA = 0.25,
      VNQ = 0.10,
      TLT = 0.10,
      IEF = 0.10,
      TIP = 0.05,
      SHY = 0.05
    ), tickers),

    Inflation_Hedge = normalise_weight(c(
      TIP = 0.30,
      DBC = 0.25,
      VNQ = 0.15,
      SPY = 0.15,
      IEF = 0.10,
      SHY = 0.05
    ), tickers),

    Crisis_Defensive = normalise_weight(c(
      TLT = 0.40,
      IEF = 0.25,
      SHY = 0.25,
      SPY = 0.10
    ), tickers),

    Real_Asset_Balanced = normalise_weight(c(
      DBC = 0.25,
      VNQ = 0.25,
      TIP = 0.20,
      SPY = 0.15,
      IEF = 0.10,
      SHY = 0.05
    ), tickers),

    Conservative_Risk = normalise_weight(c(
      SHY = 0.30,
      IEF = 0.25,
      TLT = 0.20,
      SPY = 0.15,
      EFA = 0.05,
      TIP = 0.05
    ), tickers),

    Equity_With_Bond_Hedges = normalise_weight(c(
      SPY = 0.35,
      EFA = 0.20,
      VNQ = 0.10,
      TLT = 0.15,
      IEF = 0.10,
      TIP = 0.05,
      SHY = 0.05
    ), tickers),

    Bond_RealAsset_Mix = normalise_weight(c(
      TLT = 0.30,
      IEF = 0.25,
      TIP = 0.15,
      DBC = 0.10,
      VNQ = 0.10,
      SPY = 0.05,
      SHY = 0.05
    ), tickers),

    Cash_Heavy_Defensive = normalise_weight(c(
      SHY = 0.45,
      IEF = 0.25,
      TLT = 0.15,
      TIP = 0.10,
      SPY = 0.05
    ), tickers)
  )

  random_W <- random_portfolio_library(
    tickers = tickers,
    n_portfolios = n_random_portfolios,
    max_weight = max_weight,
    min_active_weight = min_active_weight,
    seed = seed
  )

  W <- rbind(manual, random_W)
  W <- W[apply(W, 1, max) <= max_weight + 1e-12, , drop = FALSE]

  W_round <- round(W, 5)
  key <- apply(W_round, 1, paste, collapse = "_")
  W <- W[!duplicated(key), , drop = FALSE]

  rownames(W) <- make.names(rownames(W), unique = TRUE)
  W
}

build_portfolio_returns <- function(asset_returns_xts, weight_mat) {
  R <- coredata(asset_returns_xts)

  if (!all(colnames(weight_mat) %in% colnames(R))) {
    stop("Some portfolio weight columns are not in the return matrix.")
  }

  R <- R[, colnames(weight_mat), drop = FALSE]
  P <- R %*% t(weight_mat)
  colnames(P) <- rownames(weight_mat)

  xts(P, order.by = index(asset_returns_xts))
}

build_rolling_cov_array <- function(asset_returns_xts, window = 52) {
  R <- coredata(asset_returns_xts)
  h <- nrow(R)
  k <- ncol(R)

  cov_array <- array(0, dim = c(h, k, k))

  for (t in seq_len(h)) {
    if (t <= 2) {
      cov_array[t, , ] <- matrix(0, nrow = k, ncol = k)
    } else {
      start <- max(1, t - window)
      hist <- R[start:(t - 1), , drop = FALSE]

      if (nrow(hist) <= 1) {
        cov_array[t, , ] <- matrix(0, nrow = k, ncol = k)
      } else {
        cov_array[t, , ] <- cov(hist, use = "pairwise.complete.obs")
      }
    }
  }

  cov_array
}

build_portfolio_pretrade_variance <- function(asset_returns_xts,
                                              weight_mat,
                                              window = 52) {
  asset_returns_xts <- asset_returns_xts[, colnames(weight_mat)]
  cov_array <- build_rolling_cov_array(asset_returns_xts, window = window)

  h <- nrow(asset_returns_xts)
  p <- nrow(weight_mat)

  out <- matrix(0, nrow = h, ncol = p)
  colnames(out) <- rownames(weight_mat)

  for (t in seq_len(h)) {
    Sigma_t <- cov_array[t, , ]

    for (j in seq_len(p)) {
      w <- as.numeric(weight_mat[j, ])
      out[t, j] <- as.numeric(t(w) %*% Sigma_t %*% w)
    }
  }

  xts(out, order.by = index(asset_returns_xts))
}

portfolio_turnover <- function(weight_mat, prev_arm, new_arm) {
  if (is.na(prev_arm) || prev_arm == new_arm) return(0)
  sum(abs(weight_mat[new_arm, ] - weight_mat[prev_arm, ])) / 2
}

transition_penalty <- function(weight_mat,
                               prev_arm,
                               new_arm,
                               switching_cost,
                               barrier = 0) {
  if (is.null(weight_mat)) {
    if (is.na(prev_arm) || prev_arm == new_arm) return(0)
    return(switching_cost + barrier)
  }

  turnover <- portfolio_turnover(weight_mat, prev_arm, new_arm)
  switch_barrier <- ifelse(is.na(prev_arm) || prev_arm == new_arm, 0, barrier)

  switching_cost * turnover + switch_barrier
}

prepare_us_multiasset_data <- function(cfg) {
  dir.create(cfg$output_dir, recursive = TRUE, showWarnings = FALSE)

  prices_daily <- download_adjusted_prices(ETF_TICKERS, cfg$from, cfg$to)

  write.zoo(
    prices_daily,
    file = file.path(cfg$output_dir, "us_multiasset_prices_daily.csv"),
    sep = ","
  )

  prices_weekly <- build_weekly_prices(prices_daily)
  returns_weekly <- build_weekly_returns(prices_weekly)

  write.zoo(
    returns_weekly,
    file = file.path(cfg$output_dir, "us_multiasset_returns_weekly.csv"),
    sep = ","
  )

  asset_eval_var_xts <- build_pretrade_variance(
    returns_weekly,
    window = cfg$eval_var_window
  )

  weight_mat <- make_portfolio_library(
    tickers = colnames(returns_weekly),
    n_random_portfolios = cfg$n_random_portfolios,
    max_weight = cfg$max_weight,
    min_active_weight = cfg$min_active_weight,
    seed = cfg$portfolio_seed
  )

  portfolio_returns_weekly <- build_portfolio_returns(
    asset_returns_xts = returns_weekly,
    weight_mat = weight_mat
  )

  portfolio_eval_var_xts <- build_portfolio_pretrade_variance(
    asset_returns_xts = returns_weekly,
    weight_mat = weight_mat,
    window = cfg$eval_var_window
  )

  write.csv(
    weight_mat,
    file.path(cfg$output_dir, "portfolio_arm_weights.csv"),
    row.names = TRUE
  )

  write.zoo(
    portfolio_returns_weekly,
    file = file.path(cfg$output_dir, "portfolio_returns_weekly.csv"),
    sep = ","
  )

  write.zoo(
    portfolio_eval_var_xts,
    file = file.path(cfg$output_dir, "portfolio_pretrade_variance_weekly.csv"),
    sep = ","
  )

  list(
    prices_daily = prices_daily,
    prices_weekly = prices_weekly,
    returns_weekly = returns_weekly,
    asset_eval_var_xts = asset_eval_var_xts,
    weight_mat = weight_mat,
    portfolio_returns_weekly = portfolio_returns_weekly,
    portfolio_eval_var_xts = portfolio_eval_var_xts
  )
}

# 5) Finalise and summarise runs

finalise_backtest_df <- function(rets_xts,
                                 chosen_arm_id,
                                 chosen_arm,
                                 reward,
                                 switched,
                                 switching_cost,
                                 rho = 1,
                                 eval_var_xts = NULL,
                                 eval_var_cap = Inf,
                                 initial_wealth = 1,
                                 weight_mat = NULL,
                                 extra_cols = list()) {
  dates <- index(rets_xts)
  t_idx <- seq_along(dates)
  reward <- as.numeric(reward)

  if (is.null(eval_var_xts)) {
    eval_var_xts <- build_pretrade_variance(rets_xts, window = 52)
  }

  V <- coredata(eval_var_xts)
  chosen_var_raw <- as.numeric(V[cbind(t_idx, chosen_arm_id)])
  chosen_var_raw[!is.finite(chosen_var_raw)] <- 0
  chosen_var_raw <- pmax(chosen_var_raw, 0)

  chosen_var_penalty <- pmin(chosen_var_raw, eval_var_cap)

  turnover <- numeric(length(chosen_arm_id))

  if (!is.null(weight_mat)) {
    for (t in 2:length(chosen_arm_id)) {
      turnover[t] <- portfolio_turnover(
        weight_mat = weight_mat,
        prev_arm = chosen_arm_id[t - 1],
        new_arm = chosen_arm_id[t]
      )
    }
  } else {
    turnover <- as.numeric(switched)
  }

  cost_paid <- switching_cost * turnover

  # Financial return after realised transaction cost.
  net_return <- reward - cost_paid

  # Paper-aligned mean-variance objective:
  # lower-is-better loss = variance - rho * return + cost
  # higher-is-better value = rho * return - variance - cost
  mv_loss <- chosen_var_penalty - rho * reward + cost_paid
  mv_net_value <- rho * reward - chosen_var_penalty - cost_paid

  gross_return <- pmax(1 + reward, 1e-8)
  net_gross_return <- pmax(1 + net_return, 1e-8)

  log_gross_wealth <- log(initial_wealth) + cumsum(log(gross_return))
  log_net_wealth <- log(initial_wealth) + cumsum(log(net_gross_return))

  gross_wealth <- exp(log_gross_wealth)
  net_wealth <- exp(log_net_wealth)

  out <- data.frame(
    date = as.Date(dates),
    t = t_idx,
    chosen_arm_id = chosen_arm_id,
    chosen_arm = chosen_arm,
    reward = reward,
    chosen_var_raw = chosen_var_raw,
    chosen_var_penalty = chosen_var_penalty,
    switched = switched,
    turnover = turnover,
    cost_paid = cost_paid,
    net_return = net_return,
    mv_loss = mv_loss,
    mv_net_value = mv_net_value,

    # Backward-compatible aliases used by older plotting/table code.
    ra_net_value = mv_net_value,

    log_gross_wealth = log_gross_wealth,
    log_net_wealth = log_net_wealth,
    gross_wealth = gross_wealth,
    net_wealth = net_wealth,
    stringsAsFactors = FALSE
  )

  if (!is.null(weight_mat)) {
    weight_cols <- paste0("w_", make.names(colnames(weight_mat)))
    chosen_W <- weight_mat[chosen_arm_id, , drop = FALSE]

    for (j in seq_along(weight_cols)) {
      out[[weight_cols[j]]] <- chosen_W[, j]
    }
  }

  if (length(extra_cols) > 0) {
    for (nm in names(extra_cols)) {
      out[[nm]] <- extra_cols[[nm]]
    }
  }

  out$cum_mv_loss <- cumsum(out$mv_loss)
  out$cum_mv_net_value <- cumsum(out$mv_net_value)
  out$avg_mv_net_value <- out$cum_mv_net_value / out$t

  # Backward-compatible aliases.
  out$cum_ra_net_value <- out$cum_mv_net_value
  out$avg_ra_net_value <- out$avg_mv_net_value

  out$cum_cost_paid <- cumsum(out$cost_paid)
  out$cum_turnover <- cumsum(out$turnover)
  out$switches_to_date <- cumsum(out$switched)

  if ("alarm" %in% names(out)) {
    out$alarms_to_date <- cumsum(out$alarm)
  }

  out
}

summarise_backtest_run <- function(run_df, algorithm_name, initial_wealth = 1) {
  data.frame(
    algorithm = algorithm_name,

    final_cum_mv_net_value = tail(run_df$cum_mv_net_value, 1),
    final_avg_mv_net_value = tail(run_df$avg_mv_net_value, 1),
    final_cum_mv_loss = tail(run_df$cum_mv_loss, 1),

    # Backward-compatible aliases.
    final_cum_ra_net_value = tail(run_df$cum_ra_net_value, 1),
    final_avg_ra_net_value = tail(run_df$avg_ra_net_value, 1),

    final_gross_wealth = tail(run_df$gross_wealth, 1),
    final_net_wealth = tail(run_df$net_wealth, 1),
    terminal_log_net_wealth = tail(run_df$log_net_wealth, 1),

    annual_return = annualised_return_from_wealth(
      run_df$net_wealth,
      initial_wealth = initial_wealth
    ),
    annual_vol = annualised_vol(run_df$net_return),
    sharpe = sharpe_simple(run_df$net_return),
    max_drawdown = max_drawdown_simple(run_df$net_wealth),

    total_switches = sum(run_df$switched),
    switch_rate = mean(run_df$switched),
    total_turnover = sum(run_df$turnover),
    total_cost_paid = sum(run_df$cost_paid),
    cost_pct_initial = sum(run_df$cost_paid) / initial_wealth,

    total_alarms = if ("alarm" %in% names(run_df)) sum(run_df$alarm, na.rm = TRUE) else NA_real_,
    alarm_rate = if ("alarm" %in% names(run_df)) mean(run_df$alarm, na.rm = TRUE) else NA_real_,
    mean_alarm_count = if ("mean_alarm" %in% names(run_df)) sum(run_df$mean_alarm, na.rm = TRUE) else NA_real_,
    var_alarm_count = if ("var_alarm" %in% names(run_df)) sum(run_df$var_alarm, na.rm = TRUE) else NA_real_,

    stringsAsFactors = FALSE
  )
}

# 6) CUSUM 

cusum_init <- function(M = 52,
                       epsilon = 0.003,
                       h = 0.15) {
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
  y <- as.numeric(y)
  if (!is.finite(y)) y <- 0

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

# 7) Portfolio-arm bandit policies

run_ucb1_backtest <- function(rets_xts,
                              switching_cost = 0.0005,
                              warmup_weeks = 52,
                              rho = 1,
                              eval_var_xts = NULL,
                              eval_var_cap = Inf,
                              initial_wealth = 1,
                              weight_mat = NULL) {
  R <- coredata(rets_xts)
  h <- nrow(R)
  k <- ncol(R)

  N <- integer(k)
  X_sum <- numeric(k)

  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)

  prev_arm <- NA_integer_

  for (t in seq_len(h)) {
    if (t <= max(k, warmup_weeks)) {
      arm_t <- ((t - 1) %% k) + 1
    } else {
      scores <- (X_sum / pmax(N, 1)) +
        sqrt((2 * log(t)) / pmax(N, 1))

      arm_t <- which.max(scores)
    }

    chosen_id[t] <- arm_t
    chosen_name[t] <- colnames(R)[arm_t]
    rew[t] <- R[t, arm_t]
    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)

    N[arm_t] <- N[arm_t] + 1L
    X_sum[arm_t] <- X_sum[arm_t] + rew[t]

    prev_arm <- arm_t
  }

  finalise_backtest_df(
    rets_xts = rets_xts,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    eval_var_xts = eval_var_xts,
    eval_var_cap = eval_var_cap,
    initial_wealth = initial_wealth,
    weight_mat = weight_mat
  )
}

run_swucb_backtest <- function(rets_xts,
                               alpha = 0.10,
                               tau = 52,
                               switching_cost = 0.0005,
                               warmup_weeks = 52,
                               rho = 1,
                               eval_var_xts = NULL,
                               eval_var_cap = Inf,
                               initial_wealth = 1,
                               weight_mat = NULL) {
  R <- coredata(rets_xts)
  h <- nrow(R)
  k <- ncol(R)

  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)

  hist_arms <- integer(h)
  hist_rews <- numeric(h)
  prev_arm <- NA_integer_

  for (t in seq_len(h)) {
    arm_t <- NA_integer_

    if (t <= max(k, warmup_weeks)) {
      arm_t <- ((t - 1) %% k) + 1
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
    chosen_name[t] <- colnames(R)[arm_t]
    rew[t] <- R[t, arm_t]

    hist_arms[t] <- arm_t
    hist_rews[t] <- rew[t]

    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)
    prev_arm <- arm_t
  }

  finalise_backtest_df(
    rets_xts = rets_xts,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    eval_var_xts = eval_var_xts,
    eval_var_cap = eval_var_cap,
    initial_wealth = initial_wealth,
    weight_mat = weight_mat
  )
}

run_ducb_backtest <- function(rets_xts,
                              alpha = 0.10,
                              gamma = 0.997,
                              switching_cost = 0.0005,
                              warmup_weeks = 52,
                              rho = 1,
                              eval_var_xts = NULL,
                              eval_var_cap = Inf,
                              initial_wealth = 1,
                              weight_mat = NULL) {
  R <- coredata(rets_xts)
  h <- nrow(R)
  k <- ncol(R)

  N_g <- numeric(k)
  X_g <- numeric(k)
  n_g <- 0

  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)

  prev_arm <- NA_integer_

  for (t in seq_len(h)) {
    if (t <= max(k, warmup_weeks)) {
      arm_t <- ((t - 1) %% k) + 1
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
    chosen_name[t] <- colnames(R)[arm_t]
    rew[t] <- R[t, arm_t]
    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)

    N_g <- gamma * N_g
    X_g <- gamma * X_g
    n_g <- gamma * n_g + 1

    N_g[arm_t] <- N_g[arm_t] + 1
    X_g[arm_t] <- X_g[arm_t] + rew[t]

    prev_arm <- arm_t
  }

  finalise_backtest_df(
    rets_xts = rets_xts,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    eval_var_xts = eval_var_xts,
    eval_var_cap = eval_var_cap,
    initial_wealth = initial_wealth,
    weight_mat = weight_mat
  )
}

run_cd_ucb_backtest <- function(rets_xts,
                                alpha = 0.003,
                                bonus_scale = 0.60,
                                switching_cost = 0.0005,
                                M = 52,
                                epsilon = 0.0025,
                                h_thresh = 0.16,
                                warmup_weeks = 52,
                                post_alarm_pulls = 6,
                                rho = 1,
                                eval_var_xts = NULL,
                                eval_var_cap = Inf,
                                initial_wealth = 1,
                                weight_mat = NULL) {
  R <- coredata(rets_xts)
  h <- nrow(R)
  k <- ncol(R)

  N <- integer(k)
  X_sum <- numeric(k)
  X2_sum <- numeric(k)

  dets <- lapply(seq_len(k), function(i) {
    cusum_init(M, epsilon, h_thresh)
  })

  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)

  alarm_vec <- integer(h)
  forced_explore <- integer(h)
  relearn_left <- integer(k)

  prev_arm <- NA_integer_

  for (t in seq_len(h)) {
    if (t <= max(k, warmup_weeks)) {
      arm_t <- ((t - 1) %% k) + 1
    } else if (any(relearn_left > 0)) {
      arm_t <- which.max(relearn_left)
      relearn_left[arm_t] <- relearn_left[arm_t] - 1L
      forced_explore[t] <- 1L
    } else if (runif(1) < alpha) {
      arm_t <- sample.int(k, 1)
      forced_explore[t] <- 1L
    } else {
      scores <- rep(-Inf, k)
      total_N <- max(sum(N), 2)

      for (i in seq_len(k)) {
        if (N[i] > 0) {
          scores[i] <- (X_sum[i] / N[i]) +
            bonus_scale * sqrt(2 * log(total_N) / N[i])
        }
      }

      arm_t <- which.max(scores)
    }

    chosen_id[t] <- arm_t
    chosen_name[t] <- colnames(R)[arm_t]
    rew[t] <- R[t, arm_t]
    sw[t] <- ifelse(!is.na(prev_arm) && arm_t != prev_arm, 1L, 0L)

    if (N[arm_t] >= 2) {
      mu_hat <- X_sum[arm_t] / N[arm_t]
      var_hat <- safe_var(N[arm_t], X_sum[arm_t], X2_sum[arm_t])
      sd_hat <- sqrt(max(var_hat, 1e-6))
      y_for_detector <- (rew[t] - mu_hat) / sd_hat
    } else {
      y_for_detector <- rew[t]
    }

    det_out <- cusum_update(dets[[arm_t]], y_for_detector)
    dets[[arm_t]] <- det_out$state
    alarm_vec[t] <- det_out$alarm

    if (alarm_vec[t] == 1L) {
      N[arm_t] <- 1L
      X_sum[arm_t] <- rew[t]
      X2_sum[arm_t] <- rew[t]^2
      dets[[arm_t]] <- cusum_init(M, epsilon, h_thresh)
      relearn_left[arm_t] <- post_alarm_pulls
    } else {
      N[arm_t] <- N[arm_t] + 1L
      X_sum[arm_t] <- X_sum[arm_t] + rew[t]
      X2_sum[arm_t] <- X2_sum[arm_t] + rew[t]^2
    }

    prev_arm <- arm_t
  }

  finalise_backtest_df(
    rets_xts = rets_xts,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    eval_var_xts = eval_var_xts,
    eval_var_cap = eval_var_cap,
    initial_wealth = initial_wealth,
    weight_mat = weight_mat,
    extra_cols = list(
      alarm = alarm_vec,
      forced_explore = forced_explore
    )
  )
}

run_rs_sc_cusum_ucb_backtest <- function(rets_xts,
                                         alpha = 0.002,
                                         rho = 1.25,
                                         switching_cost = 0.0005,
                                         barrier = 0.00025,
                                         bonus_scale = 0.35,
                                         M_mean = 52,
                                         M_var = 52,
                                         epsilon_mean = 0.0015,
                                         epsilon_var = 0.00025,
                                         h_mean = 0.12,
                                         h_var = 0.08,
                                         warmup_weeks = 52,
                                         post_alarm_pulls = 6,
                                         eval_var_xts = NULL,
                                         eval_var_cap = Inf,
                                         initial_wealth = 1,
                                         weight_mat = NULL) {
  R <- coredata(rets_xts)
  h <- nrow(R)
  k <- ncol(R)

  V <- if (!is.null(eval_var_xts)) coredata(eval_var_xts) else NULL

  N <- integer(k)
  X_sum <- numeric(k)
  X2_sum <- numeric(k)

  det_m <- lapply(seq_len(k), function(i) {
    cusum_init(M_mean, epsilon_mean, h_mean)
  })

  det_v <- lapply(seq_len(k), function(i) {
    cusum_init(M_var, epsilon_var, h_var)
  })

  chosen_id <- integer(h)
  chosen_name <- character(h)
  rew <- numeric(h)
  sw <- integer(h)

  alarm_vec <- integer(h)
  mean_alarm <- integer(h)
  var_alarm <- integer(h)
  forced_explore <- integer(h)
  relearn_left <- integer(k)

  prev_arm <- NA_integer_

  for (t in seq_len(h)) {
    if (t <= max(k, warmup_weeks)) {
      arm_t <- ((t - 1) %% k) + 1
    } else if (any(relearn_left > 0)) {
      arm_t <- which.max(relearn_left)
      relearn_left[arm_t] <- relearn_left[arm_t] - 1L
      forced_explore[t] <- 1L
    } else if (runif(1) < alpha) {
      arm_t <- sample.int(k, 1)
      forced_explore[t] <- 1L
    } else {
      scores <- rep(-Inf, k)

      for (i in seq_len(k)) {
        if (N[i] > 0) {
          mu_hat <- X_sum[i] / N[i]
          var_hat <- safe_var(N[i], X_sum[i], X2_sum[i])

          if (!is.null(V)) {
            var_used <- V[t, i]
          } else {
            var_used <- var_hat
          }

          var_used <- ifelse(is.finite(var_used), var_used, 0)
          var_penalty <- pmin(pmax(var_used, 0), eval_var_cap)
          bonus <- bonus_scale * sqrt((2 * log(max(sum(N), 2))) / N[i])

          # Paper-aligned higher-is-better mean-variance score:
          # score = rho * estimated return - estimated variance + UCB bonus.
          score_i <- rho * mu_hat - var_penalty + bonus

          score_i <- score_i - transition_penalty(
            weight_mat = weight_mat,
            prev_arm = prev_arm,
            new_arm = i,
            switching_cost = switching_cost,
            barrier = barrier
          )

          scores[i] <- score_i
        }
      }

      arm_t <- which.max(scores)
    }

    chosen_id[t] <- arm_t
    chosen_name[t] <- colnames(R)[arm_t]
    rew[t] <- R[t, arm_t]
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

      det_m[[arm_t]] <- cusum_init(M_mean, epsilon_mean, h_mean)
      det_v[[arm_t]] <- cusum_init(M_var, epsilon_var, h_var)

      relearn_left[arm_t] <- post_alarm_pulls
    } else {
      N[arm_t] <- N[arm_t] + 1L
      X_sum[arm_t] <- X_sum[arm_t] + rew[t]
      X2_sum[arm_t] <- X2_sum[arm_t] + rew[t]^2
    }

    prev_arm <- arm_t
  }

  finalise_backtest_df(
    rets_xts = rets_xts,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = switching_cost,
    rho = rho,
    eval_var_xts = eval_var_xts,
    eval_var_cap = eval_var_cap,
    initial_wealth = initial_wealth,
    weight_mat = weight_mat,
    extra_cols = list(
      alarm = alarm_vec,
      mean_alarm = mean_alarm,
      var_alarm = var_alarm,
      forced_explore = forced_explore
    )
  )
}

# 8) Buy-and-hold ETF benchmark

run_buy_hold_etf_backtest <- function(rets_xts,
                                      arm_index,
                                      rho = 1,
                                      eval_var_xts = NULL,
                                      eval_var_cap = Inf,
                                      initial_wealth = 1) {
  R <- coredata(rets_xts)
  h <- nrow(R)

  chosen_id <- rep(arm_index, h)
  chosen_name <- rep(colnames(R)[arm_index], h)
  rew <- R[, arm_index]
  sw <- rep(0L, h)

  finalise_backtest_df(
    rets_xts = rets_xts,
    chosen_arm_id = chosen_id,
    chosen_arm = chosen_name,
    reward = rew,
    switched = sw,
    switching_cost = 0,
    rho = rho,
    eval_var_xts = eval_var_xts,
    eval_var_cap = eval_var_cap,
    initial_wealth = initial_wealth,
    weight_mat = NULL
  )
}

run_all_buy_hold_etf_backtests <- function(rets_xts,
                                           rho = 1,
                                           eval_var_xts = NULL,
                                           eval_var_cap = Inf,
                                           initial_wealth = 1) {
  k <- ncol(rets_xts)

  out <- lapply(seq_len(k), function(i) {
    run_buy_hold_etf_backtest(
      rets_xts = rets_xts,
      arm_index = i,
      rho = rho,
      eval_var_xts = eval_var_xts,
      eval_var_cap = eval_var_cap,
      initial_wealth = initial_wealth
    )
  })

  names(out) <- paste0("BH-ETF-", colnames(rets_xts))
  out
}

select_best_buy_hold_etf <- function(bh_runs,
                                     initial_wealth = 1,
                                     rank_by = c("final_net_wealth",
                                                 "final_cum_mv_net_value",
                                                 "final_cum_ra_net_value",
                                                 "sharpe")) {
  rank_by <- match.arg(rank_by)

  bh_summary <- do.call(
    rbind,
    lapply(names(bh_runs), function(nm) {
      summarise_backtest_run(
        bh_runs[[nm]],
        algorithm_name = nm,
        initial_wealth = initial_wealth
      )
    })
  )

  best_name <- bh_summary$algorithm[which.max(bh_summary[[rank_by]])]

  list(
    best_name = best_name,
    best_run = bh_runs[[best_name]],
    summary = bh_summary
  )
}

# 9) Single-seed empirical run
run_us_multiasset_backtest_one_seed <- function(cfg, 
                                                data_obj, 
                                                seed = 123) {
  set.seed(seed)

  portfolio_returns_weekly <- data_obj$portfolio_returns_weekly
  portfolio_eval_var_xts <- data_obj$portfolio_eval_var_xts
  weight_mat <- data_obj$weight_mat

  asset_returns_weekly <- data_obj$returns_weekly
  asset_eval_var_xts <- data_obj$asset_eval_var_xts

  runs <- list(
    UCB1 = run_ucb1_backtest(
      portfolio_returns_weekly,
      switching_cost = cfg$weekly_cost,
      warmup_weeks = cfg$warmup_weeks,
      rho = cfg$rs_rho,
      eval_var_xts = portfolio_eval_var_xts,
      eval_var_cap = cfg$eval_var_cap,
      initial_wealth = cfg$initial_wealth,
      weight_mat = weight_mat
    ),

    `SW-UCB` = run_swucb_backtest(
      portfolio_returns_weekly,
      alpha = cfg$sw_alpha,
      tau = cfg$sw_tau,
      switching_cost = cfg$weekly_cost,
      warmup_weeks = cfg$warmup_weeks,
      rho = cfg$rs_rho,
      eval_var_xts = portfolio_eval_var_xts,
      eval_var_cap = cfg$eval_var_cap,
      initial_wealth = cfg$initial_wealth,
      weight_mat = weight_mat
    ),

    `D-UCB` = run_ducb_backtest(
      portfolio_returns_weekly,
      alpha = cfg$du_alpha,
      gamma = cfg$du_gamma,
      switching_cost = cfg$weekly_cost,
      warmup_weeks = cfg$warmup_weeks,
      rho = cfg$rs_rho,
      eval_var_xts = portfolio_eval_var_xts,
      eval_var_cap = cfg$eval_var_cap,
      initial_wealth = cfg$initial_wealth,
      weight_mat = weight_mat
    ),

    `CUSUM-UCB` = run_cd_ucb_backtest(
      portfolio_returns_weekly,
      alpha = cfg$cd_alpha,
      bonus_scale = cfg$cd_bonus_scale,
      switching_cost = cfg$weekly_cost,
      M = cfg$cd_M,
      epsilon = cfg$cd_epsilon,
      h_thresh = cfg$cd_h,
      warmup_weeks = cfg$warmup_weeks,
      post_alarm_pulls = cfg$cd_post_alarm_pulls,
      rho = cfg$rs_rho,
      eval_var_xts = portfolio_eval_var_xts,
      eval_var_cap = cfg$eval_var_cap,
      initial_wealth = cfg$initial_wealth,
      weight_mat = weight_mat
    ),

    `RS-SC-CUSUM-UCB` = run_rs_sc_cusum_ucb_backtest(
      portfolio_returns_weekly,
      alpha = cfg$rs_alpha,
      rho = cfg$rs_rho,
      switching_cost = cfg$weekly_cost,
      barrier = cfg$rs_barrier,
      bonus_scale = cfg$rs_bonus_scale,
      M_mean = cfg$rs_M_mean,
      M_var = cfg$rs_M_var,
      epsilon_mean = cfg$rs_epsilon_mean,
      epsilon_var = cfg$rs_epsilon_var,
      h_mean = cfg$rs_h_mean,
      h_var = cfg$rs_h_var,
      warmup_weeks = cfg$warmup_weeks,
      post_alarm_pulls = cfg$rs_post_alarm_pulls,
      eval_var_xts = portfolio_eval_var_xts,
      eval_var_cap = cfg$eval_var_cap,
      initial_wealth = cfg$initial_wealth,
      weight_mat = weight_mat
    )
  )

  bh_etf_runs <- run_all_buy_hold_etf_backtests(
    rets_xts = asset_returns_weekly,
    rho = cfg$rs_rho,
    eval_var_xts = asset_eval_var_xts,
    eval_var_cap = cfg$eval_var_cap,
    initial_wealth = cfg$initial_wealth
  )

  best_bh_etf_net <- select_best_buy_hold_etf(
    bh_runs = bh_etf_runs,
    initial_wealth = cfg$initial_wealth,
    rank_by = "final_net_wealth"
  )

  best_bh_etf_mv <- select_best_buy_hold_etf(
    bh_runs = bh_etf_runs,
    initial_wealth = cfg$initial_wealth,
    rank_by = "final_cum_mv_net_value"
  )

  summary_tbl <- do.call(
    rbind,
    lapply(names(runs), function(nm) {
      summarise_backtest_run(
        runs[[nm]],
        nm,
        initial_wealth = cfg$initial_wealth
      )
    })
  )

  summary_tbl$seed <- seed
  summary_tbl <- summary_tbl[order(-summary_tbl$final_cum_mv_net_value), ]

  all_paths <- lapply(names(runs), function(nm) {
    df <- runs[[nm]]
    df$algorithm <- nm
    df$seed <- seed
    df
  })

  all_paths <- rbind_fill(all_paths)

  list(
    runs = runs,
    summary = summary_tbl,
    paths = all_paths,

    bh_etf_runs = bh_etf_runs,
    bh_etf_summary = best_bh_etf_net$summary,
    best_bh_etf_net = best_bh_etf_net,
    best_bh_etf_mv = best_bh_etf_mv,

    # Backward-compatible alias.
    best_bh_etf_ra = best_bh_etf_mv
  )
}

# 10) Multi-seed empirical run

run_us_multiasset_backtest_multiseed <- function(cfg, 
                                                 seeds = 1:50) {
  data_obj <- prepare_us_multiasset_data(cfg)

  cat(sprintf("\nNumber of weighted portfolio arms: %d\n", nrow(data_obj$weight_mat)))
  cat(sprintf("Maximum portfolio weight: %.2f\n", max(data_obj$weight_mat)))
  cat(sprintf("Mean-variance risk tolerance rho: %.4f\n\n", cfg$rs_rho))

  seed_runs <- vector("list", length(seeds))
  summary_list <- vector("list", length(seeds))
  path_list <- vector("list", length(seeds))

  for (i in seq_along(seeds)) {
    cat(sprintf("Running weighted-portfolio backtest for seed %d...\n", seeds[i]))

    one_run <- run_us_multiasset_backtest_one_seed(
      cfg = cfg,
      data_obj = data_obj,
      seed = seeds[i]
    )

    seed_runs[[i]] <- one_run
    summary_list[[i]] <- one_run$summary
    path_list[[i]] <- one_run$paths
  }

  all_summary <- rbind_fill(summary_list)
  all_paths <- rbind_fill(path_list)

  write.csv(
    all_summary,
    file.path(cfg$output_dir, "multiseed_weighted_no_iau_summary_by_seed.csv"),
    row.names = FALSE
  )

  write.csv(
    all_paths,
    file.path(cfg$output_dir, "multiseed_weighted_no_iau_paths.csv"),
    row.names = FALSE
  )

  list(
    data = data_obj,
    seeds = seeds,
    seed_runs = seed_runs,
    summary_by_seed = all_summary,
    paths_by_seed = all_paths,
    output_dir = cfg$output_dir
  )
}

# 11) Aggregate results and thesis tables

summarise_multiseed_results <- function(ms_obj) {
  df <- ms_obj$summary_by_seed
  algs <- ordered_algorithms(unique(df$algorithm))

  out <- lapply(algs, function(a) {
    sub <- df[df$algorithm == a, ]

    data.frame(
      algorithm = a,

      mean_final_cum_mv_net_value = mean(sub$final_cum_mv_net_value, na.rm = TRUE),
      sd_final_cum_mv_net_value = sd(sub$final_cum_mv_net_value, na.rm = TRUE),

      mean_final_avg_mv_net_value = mean(sub$final_avg_mv_net_value, na.rm = TRUE),
      sd_final_avg_mv_net_value = sd(sub$final_avg_mv_net_value, na.rm = TRUE),

      mean_final_cum_mv_loss = mean(sub$final_cum_mv_loss, na.rm = TRUE),
      sd_final_cum_mv_loss = sd(sub$final_cum_mv_loss, na.rm = TRUE),

      # Backward-compatible aliases.
      mean_final_cum_ra_net_value = mean(sub$final_cum_ra_net_value, na.rm = TRUE),
      sd_final_cum_ra_net_value = sd(sub$final_cum_ra_net_value, na.rm = TRUE),
      mean_final_avg_ra_net_value = mean(sub$final_avg_ra_net_value, na.rm = TRUE),
      sd_final_avg_ra_net_value = sd(sub$final_avg_ra_net_value, na.rm = TRUE),

      mean_final_net_wealth = mean(sub$final_net_wealth, na.rm = TRUE),
      sd_final_net_wealth = sd(sub$final_net_wealth, na.rm = TRUE),

      mean_annual_return = mean(sub$annual_return, na.rm = TRUE),
      sd_annual_return = sd(sub$annual_return, na.rm = TRUE),

      mean_annual_vol = mean(sub$annual_vol, na.rm = TRUE),
      sd_annual_vol = sd(sub$annual_vol, na.rm = TRUE),

      mean_sharpe = mean(sub$sharpe, na.rm = TRUE),
      sd_sharpe = sd(sub$sharpe, na.rm = TRUE),

      mean_max_drawdown = mean(sub$max_drawdown, na.rm = TRUE),
      sd_max_drawdown = sd(sub$max_drawdown, na.rm = TRUE),

      mean_total_switches = mean(sub$total_switches, na.rm = TRUE),
      sd_total_switches = sd(sub$total_switches, na.rm = TRUE),

      mean_switch_rate = mean(sub$switch_rate, na.rm = TRUE),
      sd_switch_rate = sd(sub$switch_rate, na.rm = TRUE),

      mean_total_turnover = mean(sub$total_turnover, na.rm = TRUE),
      sd_total_turnover = sd(sub$total_turnover, na.rm = TRUE),

      mean_total_cost_paid = mean(sub$total_cost_paid, na.rm = TRUE),
      sd_total_cost_paid = sd(sub$total_cost_paid, na.rm = TRUE),

      mean_total_alarms = mean(sub$total_alarms, na.rm = TRUE),
      sd_total_alarms = sd(sub$total_alarms, na.rm = TRUE),

      mean_alarm_rate = mean(sub$alarm_rate, na.rm = TRUE),
      sd_alarm_rate = sd(sub$alarm_rate, na.rm = TRUE),

      mean_mean_alarm_count = mean(sub$mean_alarm_count, na.rm = TRUE),
      sd_mean_alarm_count = sd(sub$mean_alarm_count, na.rm = TRUE),

      mean_var_alarm_count = mean(sub$var_alarm_count, na.rm = TRUE),
      sd_var_alarm_count = sd(sub$var_alarm_count, na.rm = TRUE),

      stringsAsFactors = FALSE
    )
  })

  agg <- do.call(rbind, out)
  agg <- agg[order(-agg$mean_final_cum_mv_net_value), ]

  write.csv(
    agg,
    file.path(ms_obj$output_dir, "multiseed_weighted_no_iau_summary_aggregated.csv"),
    row.names = FALSE
  )

  agg
}

build_average_weight_table <- function(paths_df) {
  weight_cols <- grep("^w_", names(paths_df), value = TRUE)
  algs <- ordered_algorithms(unique(paths_df$algorithm))

  out <- lapply(algs, function(alg) {
    sub <- paths_df[paths_df$algorithm == alg, , drop = FALSE]
    df <- data.frame(algorithm = alg, stringsAsFactors = FALSE)

    for (wc in weight_cols) {
      df[[paste0("avg_", wc)]] <- mean(sub[[wc]], na.rm = TRUE)
    }

    df
  })

  do.call(rbind, out)
}

build_portfolio_usage_table <- function(paths_df, top_n = 15) {
  algs <- ordered_algorithms(unique(paths_df$algorithm))

  out <- lapply(algs, function(alg) {
    sub <- paths_df[paths_df$algorithm == alg, ]
    tab <- sort(table(sub$chosen_arm), decreasing = TRUE)
    tab <- head(tab, top_n)

    data.frame(
      algorithm = alg,
      portfolio_arm = names(tab),
      share = as.numeric(tab) / nrow(sub),
      stringsAsFactors = FALSE
    )
  })

  do.call(rbind, out)
}

build_universe_summary <- function(returns_weekly, initial_wealth = 1) {
  R <- coredata(returns_weekly)
  dates <- index(returns_weekly)

  out <- lapply(seq_len(ncol(R)), function(i) {
    r <- R[, i]
    wealth <- initial_wealth * cumprod(1 + r)

    data.frame(
      ETF = colnames(R)[i],
      sample_start = as.Date(min(dates)),
      sample_end = as.Date(max(dates)),
      annual_return = annualised_return_from_wealth(
        wealth,
        initial_wealth = initial_wealth
      ),
      annual_vol = annualised_vol(r),
      sharpe = sharpe_simple(r),
      max_drawdown = max_drawdown_simple(wealth),
      stringsAsFactors = FALSE
    )
  })

  do.call(rbind, out)
}

build_multiseed_result_tables <- function(ms_obj, cfg) {
  dir.create(file.path(cfg$output_dir, "tables"), recursive = TRUE, showWarnings = FALSE)

  agg <- summarise_multiseed_results(ms_obj)

  main_tbl <- agg[, c(
    "algorithm",
    "mean_final_cum_mv_net_value",
    "sd_final_cum_mv_net_value",
    "mean_final_net_wealth",
    "sd_final_net_wealth",
    "mean_annual_return",
    "sd_annual_return",
    "mean_annual_vol",
    "sd_annual_vol",
    "mean_sharpe",
    "sd_sharpe",
    "mean_max_drawdown",
    "sd_max_drawdown"
  )]

  impl_tbl <- agg[, c(
    "algorithm",
    "mean_total_switches",
    "sd_total_switches",
    "mean_switch_rate",
    "sd_switch_rate",
    "mean_total_turnover",
    "sd_total_turnover",
    "mean_total_cost_paid",
    "sd_total_cost_paid",
    "mean_total_alarms",
    "sd_total_alarms",
    "mean_alarm_rate",
    "sd_alarm_rate",
    "mean_mean_alarm_count",
    "sd_mean_alarm_count",
    "mean_var_alarm_count",
    "sd_var_alarm_count"
  )]

  avg_weight_tbl <- build_average_weight_table(ms_obj$paths_by_seed)
  portfolio_usage_tbl <- build_portfolio_usage_table(ms_obj$paths_by_seed, top_n = 15)

  universe_tbl <- build_universe_summary(
    ms_obj$data$returns_weekly,
    initial_wealth = cfg$initial_wealth
  )

  bh_etf_tbl <- ms_obj$seed_runs[[1]]$bh_etf_summary

  write.csv(
    main_tbl,
    file.path(cfg$output_dir, "tables", "weighted_no_iau_emp_summary_main.csv"),
    row.names = FALSE
  )

  write.csv(
    impl_tbl,
    file.path(cfg$output_dir, "tables", "weighted_no_iau_emp_summary_implementation.csv"),
    row.names = FALSE
  )

  write.csv(
    avg_weight_tbl,
    file.path(cfg$output_dir, "tables", "weighted_no_iau_emp_average_etf_weights.csv"),
    row.names = FALSE
  )

  write.csv(
    portfolio_usage_tbl,
    file.path(cfg$output_dir, "tables", "weighted_no_iau_emp_portfolio_usage_top15.csv"),
    row.names = FALSE
  )

  write.csv(
    universe_tbl,
    file.path(cfg$output_dir, "tables", "weighted_no_iau_emp_etf_universe_summary.csv"),
    row.names = FALSE
  )

  write.csv(
    bh_etf_tbl,
    file.path(cfg$output_dir, "tables", "weighted_no_iau_emp_bh_etf_summary.csv"),
    row.names = FALSE
  )

  list(
    main_tbl = main_tbl,
    impl_tbl = impl_tbl,
    avg_weight_tbl = avg_weight_tbl,
    portfolio_usage_tbl = portfolio_usage_tbl,
    universe_tbl = universe_tbl,
    bh_etf_tbl = bh_etf_tbl,
    aggregated = agg
  )
}

# 12) Mean path

build_multiseed_path_summary <- function(paths_df, value_col) {
  algs <- ordered_algorithms(unique(paths_df$algorithm))
  out <- vector("list", length(algs))

  for (i in seq_along(algs)) {
    sub <- paths_df[paths_df$algorithm == algs[i], ]
    times <- sort(unique(sub$t))

    mean_v <- numeric(length(times))
    dates_j <- as.Date(sub[match(times, sub$t), "date"])

    for (j in seq_along(times)) {
      vals <- sub[sub$t == times[j], value_col]
      vals <- vals[is.finite(vals)]
      mean_v[j] <- if (length(vals) == 0) NA_real_ else mean(vals)
    }

    out[[i]] <- data.frame(
      t = times,
      date = dates_j,
      algorithm = algs[i],
      mean = mean_v,
      stringsAsFactors = FALSE
    )
  }

  do.call(rbind, out)
}

build_multiseed_drawdown_summary <- function(paths_df) {
  algs <- ordered_algorithms(unique(paths_df$algorithm))
  seeds <- unique(paths_df$seed)

  dd_list <- list()
  idx <- 1

  for (alg in algs) {
    for (sd in seeds) {
      sub <- paths_df[paths_df$algorithm == alg & paths_df$seed == sd, ]
      sub <- sub[order(sub$t), ]

      running_max <- cummax(sub$net_wealth)
      dd <- sub$net_wealth / running_max - 1

      dd_list[[idx]] <- data.frame(
        t = sub$t,
        date = sub$date,
        algorithm = alg,
        seed = sd,
        drawdown = dd,
        stringsAsFactors = FALSE
      )

      idx <- idx + 1
    }
  }

  dd_all <- do.call(rbind, dd_list)

  out <- lapply(algs, function(alg) {
    sub <- dd_all[dd_all$algorithm == alg, ]
    times <- sort(unique(sub$t))

    mean_v <- numeric(length(times))
    dates_j <- as.Date(sub[match(times, sub$t), "date"])

    for (j in seq_along(times)) {
      vals <- sub[sub$t == times[j], "drawdown"]
      vals <- vals[is.finite(vals)]
      mean_v[j] <- if (length(vals) == 0) NA_real_ else mean(vals)
    }

    data.frame(
      t = times,
      date = dates_j,
      algorithm = alg,
      mean = mean_v,
      stringsAsFactors = FALSE
    )
  })

  do.call(rbind, out)
}

# 13) Plots: five algorithms + BH-ETF

plot_multiseed_net_wealth <- function(ms_obj,
                                      file,
                                      include_bh_etf = TRUE,
                                      show_title = FALSE) {
  df <- build_multiseed_path_summary(ms_obj$paths_by_seed, "net_wealth")
  algs <- ordered_algorithms(unique(df$algorithm))
  cols <- policy_colours(algs)

  xr <- range(df$date, na.rm = TRUE)
  yr <- range(df$mean, na.rm = TRUE)

  if (include_bh_etf) {
    bh_etf <- ms_obj$seed_runs[[1]]$best_bh_etf_net$best_run
    yr <- range(c(yr, bh_etf$net_wealth), na.rm = TRUE)
  }

  png(file, width = 1200, height = 750, res = 120)
  on.exit(dev.off(), add = TRUE)

  plot(
    NA,
    xlim = xr,
    ylim = yr,
    xlab = "Date",
    ylab = "Mean net wealth",
    main = ifelse(show_title, "Weighted Portfolio Bandit Backtest: Mean Net Wealth", ""),
    xaxt = "n"
  )

  axis.Date(1, at = seq(xr[1], xr[2], by = "2 years"), format = "%Y")
  grid(col = "grey85", lty = "dotted")

  for (alg in algs) {
    sub <- df[df$algorithm == alg, ]
    lines(sub$date, sub$mean, col = cols[alg], lwd = 2)
  }

  legend_labels <- algs
  legend_cols <- unname(cols[algs])
  legend_lty <- rep(1, length(algs))
  legend_lwd <- rep(2, length(algs))

  if (include_bh_etf) {
    bh_etf <- ms_obj$seed_runs[[1]]$best_bh_etf_net$best_run
    bh_etf_name <- ms_obj$seed_runs[[1]]$best_bh_etf_net$best_name

    lines(
      bh_etf$date,
      bh_etf$net_wealth,
      col = "#4574B4",
      lwd = 2,
      lty = 2
    )

    legend_labels <- c(legend_labels, bh_etf_name)
    legend_cols <- c(legend_cols, "#4574B4")
    legend_lty <- c(legend_lty, 2)
    legend_lwd <- c(legend_lwd, 2)
  }

  legend(
    "topleft",
    legend = legend_labels,
    col = legend_cols,
    lty = legend_lty,
    lwd = legend_lwd,
    bty = "n",
    cex = 0.80
  )
}

plot_multiseed_cum_mv_value <- function(ms_obj,
                                        file,
                                        include_bh_etf = TRUE,
                                        show_title = FALSE) {
  df <- build_multiseed_path_summary(ms_obj$paths_by_seed, "cum_mv_net_value")
  algs <- ordered_algorithms(unique(df$algorithm))
  cols <- policy_colours(algs)

  xr <- range(df$date, na.rm = TRUE)
  yr <- range(df$mean, na.rm = TRUE)

  if (include_bh_etf) {
    bh_etf <- ms_obj$seed_runs[[1]]$best_bh_etf_mv$best_run
    yr <- range(c(yr, bh_etf$cum_mv_net_value), na.rm = TRUE)
  }

  png(file, width = 1200, height = 750, res = 120)
  on.exit(dev.off(), add = TRUE)

  plot(
    NA,
    xlim = xr,
    ylim = yr,
    xlab = "Date",
    ylab = "Mean cumulative MV net value",
    main = ifelse(show_title, "Weighted Portfolio Bandit Backtest: Cumulative MV Net Value", ""),
    xaxt = "n"
  )

  axis.Date(1, at = seq(xr[1], xr[2], by = "2 years"), format = "%Y")
  grid(col = "grey85", lty = "dotted")

  for (alg in algs) {
    sub <- df[df$algorithm == alg, ]
    lines(sub$date, sub$mean, col = cols[alg], lwd = 2)
  }

  legend_labels <- algs
  legend_cols <- unname(cols[algs])
  legend_lty <- rep(1, length(algs))
  legend_lwd <- rep(2, length(algs))

  if (include_bh_etf) {
    bh_etf <- ms_obj$seed_runs[[1]]$best_bh_etf_mv$best_run
    bh_etf_name <- ms_obj$seed_runs[[1]]$best_bh_etf_mv$best_name

    lines(
      bh_etf$date,
      bh_etf$cum_mv_net_value,
      col = "#4574B4",
      lwd = 2,
      lty = 2
    )

    legend_labels <- c(legend_labels, bh_etf_name)
    legend_cols <- c(legend_cols, "#4574B4")
    legend_lty <- c(legend_lty, 2)
    legend_lwd <- c(legend_lwd, 2)
  }

  legend(
    "topleft",
    legend = legend_labels,
    col = legend_cols,
    lty = legend_lty,
    lwd = legend_lwd,
    bty = "n",
    cex = 0.80
  )
}

# Backward-compatible wrapper with old function name
plot_multiseed_cum_ra_value <- function(ms_obj,
                                        file,
                                        include_bh_etf = TRUE,
                                        show_title = FALSE) {
  plot_multiseed_cum_mv_value(
    ms_obj = ms_obj,
    file = file,
    include_bh_etf = include_bh_etf,
    show_title = show_title
  )
}

plot_multiseed_drawdown <- function(ms_obj,
                                    file,
                                    include_bh_etf = TRUE,
                                    show_title = FALSE) {
  df <- build_multiseed_drawdown_summary(ms_obj$paths_by_seed)
  algs <- ordered_algorithms(unique(df$algorithm))
  cols <- policy_colours(algs)

  xr <- range(df$date, na.rm = TRUE)
  yr <- range(c(0, df$mean), na.rm = TRUE)

  if (include_bh_etf) {
    bh_etf <- ms_obj$seed_runs[[1]]$best_bh_etf_net$best_run
    dd_etf <- bh_etf$net_wealth / cummax(bh_etf$net_wealth) - 1
    yr <- range(c(yr, dd_etf), na.rm = TRUE)
  }

  png(file, width = 1200, height = 750, res = 120)
  on.exit(dev.off(), add = TRUE)

  plot(
    NA,
    xlim = xr,
    ylim = yr,
    xlab = "Date",
    ylab = "Mean drawdown",
    main = ifelse(show_title, "Weighted Portfolio Bandit Backtest: Mean Drawdown", ""),
    xaxt = "n"
  )

  axis.Date(1, at = seq(xr[1], xr[2], by = "2 years"), format = "%Y")
  grid(col = "grey85", lty = "dotted")

  for (alg in algs) {
    sub <- df[df$algorithm == alg, ]
    lines(sub$date, sub$mean, col = cols[alg], lwd = 2)
  }

  legend_labels <- algs
  legend_cols <- unname(cols[algs])
  legend_lty <- rep(1, length(algs))
  legend_lwd <- rep(2, length(algs))

  if (include_bh_etf) {
    bh_etf <- ms_obj$seed_runs[[1]]$best_bh_etf_net$best_run
    bh_etf_name <- ms_obj$seed_runs[[1]]$best_bh_etf_net$best_name
    dd_etf <- bh_etf$net_wealth / cummax(bh_etf$net_wealth) - 1

    lines(
      bh_etf$date,
      dd_etf,
      col = "#4574B4",
      lwd = 2,
      lty = 2
    )

    legend_labels <- c(legend_labels, bh_etf_name)
    legend_cols <- c(legend_cols, "#4574B4")
    legend_lty <- c(legend_lty, 2)
    legend_lwd <- c(legend_lwd, 2)
  }

  legend(
    "bottomleft",
    legend = legend_labels,
    col = legend_cols,
    lty = legend_lty,
    lwd = legend_lwd,
    bty = "n",
    cex = 0.80
  )
}

# 14) Run

ms_bt <- run_us_multiasset_backtest_multiseed(
  cfg = cfg,
  seeds = 1:100
)

ms_tables <- build_multiseed_result_tables(ms_bt, cfg)

print(ms_tables$main_tbl)
print(ms_tables$impl_tbl)
print(ms_tables$avg_weight_tbl)
print(ms_tables$bh_etf_tbl)

# Graphs WITH BH-ETF
plot_multiseed_net_wealth(
  ms_obj = ms_bt,
  file = file.path(cfg$output_dir, "weighted_no_iau_net_wealth_with_bh_etf.png"),
  include_bh_etf = TRUE
)

plot_multiseed_cum_mv_value(
  ms_obj = ms_bt,
  file = file.path(cfg$output_dir, "weighted_no_iau_cum_mv_value_with_bh_etf.png"),
  include_bh_etf = TRUE
)

plot_multiseed_drawdown(
  ms_obj = ms_bt,
  file = file.path(cfg$output_dir, "weighted_no_iau_drawdown_with_bh_etf.png"),
  include_bh_etf = TRUE
)

# Graphs WITHOUT BH-ETF

plot_multiseed_net_wealth(
  ms_obj = ms_bt,
  file = file.path(cfg$output_dir, "weighted_no_iau_net_wealth_algorithms_only.png"),
  include_bh_etf = FALSE
)

plot_multiseed_cum_mv_value(
  ms_obj = ms_bt,
  file = file.path(cfg$output_dir, "weighted_no_iau_cum_mv_value_algorithms_only.png"),
  include_bh_etf = FALSE
)

plot_multiseed_drawdown(
  ms_obj = ms_bt,
  file = file.path(cfg$output_dir, "weighted_no_iau_drawdown_algorithms_only.png"),
  include_bh_etf = FALSE
)