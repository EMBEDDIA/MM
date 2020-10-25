#' Multivariate normal mixture conditional likelihood model
#'
#' Gibbs sampling from the multivariate normal mixture conditional likelihood 
#' model.
#' 
#' @param y_train factor. Categorical response in the train data.
#' @param s_train matrix. Probabilistic predictions of candidate models for 
#' train data, binded by columns.
#' @param s_test matrix. Probabilistic predictions of candidate models for test 
#' data, binded by columns.
#' @param n_c numeric. Number of classes of the response.
#' @param n_s numeric. Number of candidate models.
#' @param iter numeric. Number of iterations for Gibbs sampling.
#' @param n_g numeric. Number of mixtures at the beginning of Gibbs sampling. 
#' Redundant mixtures will collapse during sampling.
#' @param invalog logical. If TRUE, transform s_train and s_test with the 
#' inverse logistic transformation. Defaults to TRUE.
#' @param prior_s2 numeric. Prior on the diagonal of the inverse-Wishart scale 
#' matrix for covariance matrices.
#' @param prior_mu numeric. Prior on the means of latent multivariate normal 
#' distributions.
#' @param prior_nu numeric. Prior on the inverse-Wishart degrees of freedom for 
#' covariance matrices.
#'
#' @return Matrix with posterior means of probabilistic predictions for each 
#' test observation. The number of columns is n_c and the number of rows is the 
#' same as nrow(s_test).
#'
#' @examples
#' set.seed(1)
#' n <- 1000
#' t <- sample(1:2, n, replace = T)
#' M1 <- vector(mode = "numeric", length = n)
#' M2 <- vector(mode = "numeric", length = n)
#' 
#' nt1 <- sum(t == 1)
#' nt2 <- n - nt1
#' 
#' # Candidate model predictions
#' # M1: systematic error
#' # M2: random
#' M1[t == 1] <- rbeta(nt1, 1, 2)
#' M2[t == 1] <- rbeta(nt1, 2, 2)
#' M1[t == 2] <- rbeta(nt2, 2, 1)
#' M2[t == 2] <- rbeta(nt2, 1, 1)
#' 
#' p         <- matrix(c(M1, 1-M1, M2, 1-M2), ncol = 4)
#' train_ind <- 1:500
#' test_ind  <- 501:1000
#' 
#' t_train <- t[train_ind]
#' t_test  <- t[test_ind]
#' p_train <- p[train_ind, ]
#' p_test  <- p[test_ind, ]
#' 
#' MM_fit <- model_MM(t_train, p_train, p_test, n_c = 2, n_s = 2)
#' 
#' 
#' @references Pirs, G. and Strumbelj, E. (2019). Bayesian Combination of 
#' Probabilistic Classifiers using Multivariate Normal Mixtures. Journal of 
#' Machine Learning Research, 20, 51-1.
#'
#' @export
model_MM <- function (y_train, s_train, s_test, n_c, n_s,
                            iter       = 100, 
                            n_g        = 15,
                            invalog    = T,
                            regularize = F,
                            # priors
                            prior_s2   = 100,
                            prior_mu   = 0,
                            prior_nu   = 2 + (n_c - 1) * n_s
) {
  library(mvtnorm)
  library(MASS)
  
  invalog_transform <- function (x, n_s, n_c) {
    for (i in 1:n_s) {
      lo <- (i-1)*n_c + 1
      hi <- (i-1)*n_c + n_c
      x[,lo:hi] <- x[,lo:hi] + runif(nrow(x[,lo:hi]) * ncol(x[,lo:hi]), 0.00,0.001)
      x[,lo:hi] <- x[,lo:hi] / rowSums(x[,lo:hi])
      
      for (j in 1:n_c) {
        x[ ,(i-1)*n_c + j] <- log(x[ ,(i-1)*n_c + j] / x[ ,(i-1)*n_c+n_c])
      }
    }
    x[,(1:ncol(x) %% n_c) != 0]
  }
  
  vec_prod  <- function(vec) {return(vec %*% t(vec))}
  
  to_matrix <- function(vec) {return(matrix(vec, 
                                            ncol = sqrt(length(vec)), 
                                            byrow = TRUE))}
  
  sum_na    <- function (my_vec) {return (sum(is.na(my_vec)))}
  if (invalog) {
    t_train <- invalog_transform(s_train, n_s, n_c)
    t_test  <- invalog_transform(s_test, n_s, n_c)
  } else {
    x <- seq(1, ncol(s_train), n_c)
    t_train <- s_train[,-x]
    t_test  <- s_test[,-x]
  }
  t_all   <- rbind(t_train, t_test)
  
  collapsed <- array(F, dim = c(n_c, n_g)) 
  
  # priors ----
  nu_0       <- prior_nu
  Sigma_0    <- diag(prior_s2, ncol(t_train))
  S_0        <- diag(prior_s2, ncol(t_train))
  mu_0       <- rep(prior_mu, ncol(t_train))
  invSigma_0 <- solve(Sigma_0) # Prepare the inverse of the prior.
  
  # parameters ----
  par_y_test <- array(NA, dim = c(iter+1, nrow(t_test)))
  par_p_test <- array(NA, dim = c(iter+1, nrow(t_test), n_c))
  par_predict<- array(NA, dim = c(iter+1, nrow(t_test), n_c))
  par_group  <- array(NA, dim = c(iter+1, nrow(t_test) + nrow(t_train)))
  par_mu     <- array(NA, dim = c(iter+1, n_c, n_g, ncol(t_train)))
  par_invSigma  <- array(NA, dim = c(iter+1, n_c, n_g, ncol(t_train), ncol(t_train)))
  
  
  # assignment of starting values ----
  par_y_test[1,] <- sample(1:n_c, nrow(t_test), rep = T)
  par_group[1,]  <- sample(1:n_g, nrow(t_test) + nrow(t_train), rep = T)
  
  par_mu[1,,,] <- 0
  for (j in 1:n_c) {
    for (k in 1:n_g) {
      par_invSigma[1,j,k,,] <- diag(ncol(t_train))
    }
  }
  
  COMPLETE_DATA <- F
  
  # main loop ----
  for (i in 2:(iter + 1)) {  
    cat(i, " ")

    y_all <- c(y_train, par_y_test[i-1,])
    # mu and Sigma ----
    for (j in 1:n_c) {
      # collapse groups
      for (k in n_g:1) {
        
        if (COMPLETE_DATA) {
          if (sum(par_group[i-1,] == k & y_all == j) <= 1) {
            collapsed[j,k] <- T
          }
        } else {
          if (sum(par_group[i-1,1:length(y_train)][y_train == j] == k) <= 1) {
            collapsed[j,k] <- T
          }          
        }
      }

      
      # sample new params
      for (k in 1:n_g) if (!collapsed[j,k]) {

        # get data for this class and this group
        if (COMPLETE_DATA) {
          tmp_t_all <- t_all[y_all == j & par_group[i - 1, ] == k,]
        } else {
          tmp_t_all <- t_train[y_train == j & par_group[i-1,1:length(y_train)] == k,]
        }
        
        n_j       <- nrow(tmp_t_all)
        
        # Get values from the previous iteration.
        invSigma_j <- par_invSigma[i-1,j,k,,]
        mu_j     <- par_mu[i-1,j,k,] 
        Sigma_n  <- solve(invSigma_0 + n_j*invSigma_j)
        umean    <- colMeans(tmp_t_all)
        
 
        mu_n     <- Sigma_n %*% (invSigma_0 %*% mu_0 + 
                                   n_j * invSigma_j %*% umean)
        mu_j     <- mvrnorm(1, mu_n, Sigma_n)
        nu_n     <- nu_0 + n_j
        mu_mat   <- matrix(rep(mu_j, n_j), ncol = length(mu_j), byrow=TRUE)
        ecm      <- t(as.matrix(tmp_t_all - mu_mat))
        ecm      <- apply(ecm, 2, vec_prod)
        ecm      <- rowSums(ecm)
        ecm      <- matrix(ecm, ncol = length(mu_j), byrow = TRUE)
        S_n      <- S_0 + ecm
        invSigma_j <- rWishart(1, nu_n, solve(S_n))[,,1]
        
        # Insert new values into the current iteration.
        
        par_mu[i,j,k,]     <- mu_j
        par_invSigma[i,j,k,,] <- invSigma_j
      }
    }
    
    # groups ----
    par_group[i,] <- par_group[i-1,]
    group_all <- par_group[i,1:length(y_train)]
    g_probs <- array(0, dim = c(nrow(t_train), n_g))
    for (j in 1:n_c) {
      idxs      <- y_train == j
      tmp_t_all <- t_train[idxs,]
      for (k in 1:n_g) if (!collapsed[j,k]) {
        mu     <- par_mu[i,j,k,]
        Sigma  <- solve(par_invSigma[i,j,k,,])
        g_probs[idxs,k] <- dmvnorm(tmp_t_all, mean = mu, sigma = Sigma) 
      }
    }

    g_probs <- g_probs / rowSums(g_probs)
    par_group[i,1:length(y_train)] <- apply(g_probs, 1, function(x){sample(1:n_g, 1, prob = x)})

    get_pred <- function(t_test, y_all, n_c, n_g, collapsed, par_mu, par_invSigma, group_all, lambda = rep(0, ncol(t_test))) {
      pred <- array(0, dim = c(nrow(t_test), n_c, n_g))
      for (j in 1:n_c) {
        for (k in 1:n_g) if (!collapsed[j,k]) {
          mu     <- par_mu[i,j,k,]
          Sigma  <- solve(par_invSigma[i,j,k,,])  + diag(lambda)
          
          pred[,j,k] <- dmvnorm(t_test, mean = mu, sigma = Sigma) * sum(group_all == k & y_all == j)
        }
      }

      pred <- sweep(pred, 1, apply(pred, 1, sum), FUN="/")
    }
    pred <- get_pred(t_test, y_train, n_c, n_g, collapsed, par_mu, par_invSigma, par_group[i,1:length(y_train)])
    tmp  <- apply(pred, 1, function(x){sample(1:(n_c * n_g), 1, prob = c(x))})
    par_y_test[i,] <- (tmp - 1) %% n_c + 1
    par_group[i,(length(y_train) + 1):length(par_group[i,])] <- floor((tmp - 1) / n_c) + 1

    # regularize
    fn_optim <- function(x, t_train, y_train, n_c, n_g, collapsed, par_mu, par_invSigma, par_group) {
      pred <- get_pred(t_train, y_train, n_c, n_g, collapsed, par_mu, par_invSigma, par_group, lambda = x)
      pred <-  apply(pred, c(1,2), sum)
      p_star <- pred[cbind(1:nrow(pred), y_train)]
      -mean(log(p_star))
    }
    
    if (regularize) {
      lambda <- rep(0, ncol(t_train))
      idx    <- sample(1:length(y_train), 100, rep = T)
      lambda_max <- 100000
      res <- optim(lambda, fn = fn_optim, 
                   lower = rep(0, length(lambda)),
                   upper = rep(lambda_max, length(lambda)),
                   method = "L-BFGS-B", #control = list(trace = 1),
                   t_train = t_train[idx,], y_train = y_train[idx], n_c = n_c,
                   n_g = n_g, collapsed = collapsed, par_mu = par_mu, par_invSigma = par_invSigma, par_group = par_group[i,1:length(y_train)][idx])
      
      pred <- get_pred(t_test, y_train, n_c, n_g, collapsed, par_mu, par_invSigma, par_group[i,1:length(y_train)], lambda = res$par)
      par_predict[i,,] <- apply(pred, c(1,2), sum)
      
    } else {
      par_predict[i,,] <- apply(pred, c(1,2), sum)
    }
  }
  cat("\n")
  
  return(pred = apply(par_predict[-1,,], c(2,3), mean))
}