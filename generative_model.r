library(plyr)
library(dplyr)
library(mvtnorm)
library(reshape2)

#library(devtools)
#install_github("dgrtwo/gganimate")
#install_github("mcandocia/animation", ref="patch-1")#this has a bug fix that prevents convert.exe from working in Windows
#install.packages('magick')

#clustering will use blocks of variables:

## numeric-numeric (numeric)
# all separate mean estimations
# multivariate normal distribution, with possible restrictions:
# * constant variance & no covariance
# * varying variance by class & no covariance
# * varying variance same for all classes & no covariance
# * free covariance same for all classes
# * free covariance different for all classes

## categorical-categorical
# smoothing coefficients to avoid 0 probabilities
# 1-category probabilities
# interaction effects between categories to be manually supplied (or 'all') - not recommended since sparsity becomes apparent

## categorical-numeric
# none at the moment, since that greatly increases complexity and convolutes previous  numeric-numeric configs

## priors
# priors are initially even or can be pre-set; they can also be fixed to a pre-set value (or even)
# smoothing constant for priors can be indicated

## initial categories
# indexes of  initial groups can be supplied
# fixing of those groups can be controlled
# prior estimate can be based off that

#check for group variables
is.positive <- function(x){
  !(is.na(x) | x <= 0 )
}

#numeric calculations

geom.mean <- function(x){
  prod(x) ^ (1/length(x))
}

mean.center <- function(x, groups){
  x = as.numeric(x) %>% as.data.frame()
  x$groups = groups
  names(x) = c('x', 'groups')
  ndf = (x %>% group_by(groups) %>% mutate(z = x-mean(x)) %>% ungroup() %>% select(z))$z %>% as.numeric()
  return(ndf)
}

#used to standardize across groups
mean.centered.covariance <- function(data, groups, covariance_constraint){
  n_vars = ncol(data)
  centered.data = colwise(mean.center)(data, groups=groups)
  covariance_matrix = constrained.covariance(centered.data, covariance_constraint)
  return(covariance_matrix)
}

#used for individual groups
constrained.covariance <- function(data, covariance_constraint){
  n_vars = ncol(data)
  covariance_matrix = var(data)
  if (covariance_constraint[1]=='unit'){
    covariance_matrix = diag(n_vars) * geom.mean(diag(covariance_matrix))
  }
  else if (covariance_constraint[1]=='free_diagonal'){
    covariance_matrix = diag(covariance_matrix) * diag(n_vars)
  }
  rownames(covariance_matrix) = colnames(covariance_matrix) = names(data)
  return(covariance_matrix)
}

#categorical estimators
class.estimate <- function(x, lambda){
  tab = as.numeric(table(x))
  names(tab) = levels(x)
  tab = tab + lambda
  tab/sum(tab)
}

all.class.estimates <- function(data, lambda){
  results = list()
  for (colname in names(data)){
    results[[colname]] = class.estimate(data[,colname], lambda)
  }
  return(results)
}

calc.class.probabilities <- function(x, loadings){
  return(loadings[as.numeric(x)])
}

calc.all.class.probabilities <- function(data, loadings){
  probs = numeric(nrow(data))
  for (column in names(data)){
    probs = probs + log(calc.class.probabilities(data[,column], loadings[[column]]))
  }
  return(probs)
}

## Function performs unsupervised, semi-supervised, or supervised clustering/classification based on 
## multivariate normal distributions and bayesian components for categorical variables
# data - data frame with rows to cluster
# variables - names of variables to use as clustering criteria; defaults to all
# n_groups - number of clusters to make
# n_iter - number of iterations to perform
# interaction_class_variables - factor variables to combine as a pair instead of considering individually
# covariance_across_classes - 'different' if each class can have its own covariance, 'constant' otherwise
# covariance_constraint - 'free' = covariance can have any values; 'free_diagonal' = each variable can have its own variance, but no correlations; 'unit' = all variables have same variance, no correlation
# initial_priors - initial priors to give to groups; not particularly useful
# fix_priors - Do not change priors after they have been set, either evenly (default), manually (initial_priors=TRUE), or if estimate_prior_from_initial_groups=TRUE
# initial_groups - Initial groups for each cluster; used in semi-supervised and supervised model
# keep_initial_groups - Indicates whether or not the initial groups will be forced to be kept after the first iteration; default TRUE
# estimate_prior_from_initial_groups - Indicates whether or not the first prior (whether fixed or not) should be estimated from the proportions among the initial groups
# prior_smoothing_constant - A (usually small) constant to ensure all prior probabilities are >0
# class_smoothing_constant - A (usually small) constant to ensure all factor-based probabilities are >0
# class_interaction_smoothing_constant - A (usually small) constant to ensure all interactions of factor-based probabilities are >0
# record_history - Indicates whether or not the classes & loadings at each iteration should be kept; default False, required for plotting over time
# include_classes_in_history - Toggles the inclusion of classes in loading history; default True
# include_data_copy - Whether or not you want to include a copy of the data in the resulting model; required for expanding history
generative_model <- function(data, variables=names(data), n_groups, n_iter = 30, 
                      interaction_class_variables = NULL,
                      covariance_across_classes=c('different', 'constant'),
                      covariance_constraint=c('free_diagonal','free','unit'),
                      initial_priors=NULL,
                      fix_priors=FALSE,
                      initial_groups=NULL,
                      keep_initial_groups=!is.null(initial_groups),
                      estimate_prior_from_initial_groups=FALSE,
                      prior_smoothing_constant=0.01,
                      class_smoothing_constant=0.01,
                      class_interaction_smoothing_constant=0.05, 
                      record_history=FALSE,
                      include_classes_in_history=TRUE,
                      include_data_copy=record_history){
  #determine categorical and numeric variables
  numeric_variables = variables[unlist(colwise(is.numeric)(data[,variables]))]
  categorical_variables = variables[unlist(colwise(is.discrete)(data[,variables]))]
  original_data = data
  #add interaction classes if necessary
  interaction_varnames = character(0)
  if (!is.null(interaction_class_variables)){
    for (pair in interaction_class_variables){
      new_varname = paste(pair, collapse=':')
      data[,new_varname] = factor(paste(as.character(data[,pair[1]]), 
                                        as.character(data[,pair[2]])),
                                  collapse=':')
      interaction_varnames = c(interaction_varnames, new_varname)
      #remove variables from pair
      categorical_variables = categorical_variables[!categorical_variables %in% pair]
    }
  }
  
  #initialize priors
  if (is.null(initial_priors) & !estimate_prior_from_initial_groups){
    priors = rep(1/n_groups, n_groups)
  }
  else if (estimate_prior_from_initial_groups){
    if (is.null(initial_groups)){
      stop('Initial groups must be specified if `estimate_prior_from_initial_groups` is `TRUE`')
    }
    prior_vals = as.numeric(table(initial_groups[is.positive(initial_groups)]))
    priors = prior_vals/sum(prior_vals)
  }
  else{
    priors = initial_priors
  }
  
  #initialize groups
  if (!is.null(initial_groups)){
    if (all(is.positive(initial_groups))){
      data$group = initial_groups
    }
    else{
      data$group = ifelse(is.positive(initial_groups), initial_groups, sample(1:n_groups, nrow(data), replace=TRUE, prob=priors))
    }
  }
  else{
    data$group = sample(1:n_groups, nrow(data), replace=TRUE, prob=priors)
  }
  n_rows = nrow(data)
  

  
  #initialize coefficients
  #define
  gmean = list()
  gvar = list()
  gclass = list()
  gclass_interaction = list()
  ##iterate
  #numeric
  #if equal variance
  if (covariance_across_classes[1]=='constant'){
    covariance_matrix = mean.centered.covariance(data[,numeric_variables], data$group, covariance_constraint)
    for (g in 1:n_groups){
      subdata = data %>% filter(group==g)
      gmean[[g]] = as.numeric(colMeans(subdata[,numeric_variables]))
      names(gmean[[g]]) = numeric_variables
      gvar[[g]] = covariance_matrix
    }
    
  }
  #if unequal variance
  else{
    for (g in 1:n_groups){
      subdata = data %>% filter(group==g)
      gmean[[g]] = as.numeric(colMeans(subdata[,numeric_variables]))
      names(gmean[[g]]) = numeric_variables
      gvar[[g]] = constrained.covariance(subdata[,numeric_variables], covariance_constraint)
    }
  }
  #categorical estimates
  for (g in 1:n_groups){
   gclass[[g]] = all.class.estimates(data[,categorical_variables], lambda=class_smoothing_constant)
   if (length(interaction_varnames) > 0){
     gclass_interaction[[g]] = all.class.estimates(data[,interaction_variables], lambda=class_interaction_smoothing_constant)
   }
    
  }
  
  #initialize last necessary structures
  history = list()
  probs = matrix(nrow=nrow(data), ncol=n_groups)
  if (record_history){
    if (include_classes_in_history){
      group_copy = data$group
    }
    else{
      group_copy=NULL
    }
    entry = list(classes = group_copy, mu = gmean, sigma = gvar, class_prop = gclass, class_prop_interaction = gclass_interaction,
                 priors = priors)
    history[[1]] = entry
  }
  
  #iterate
  for (i in 1:(n_iter+1)){
    #calculate new probs
    for (g in 1:n_groups){
      #prior initialization
      probs[,g] = log(priors[g])
      #multivariate normal contribution
      if (length(numeric_variables) > 0)
        probs[,g] = probs[,g] + log(dmvnorm(data[,numeric_variables], mean=gmean[[g]], sigma = gvar[[g]]))
      #categorical contribution
      if (length(categorical_variables) > 0){
        probs[,g] = probs[,g] + calc.all.class.probabilities(data[,categorical_variables], gclass[[g]])
      }
      #interaction effects
      if (length(interaction_varnames) > 0){
        probs[,g] = probs[,g] + calc.all.class.probabilities(data[,interaction_varnames], gclass[[g]])
      }
    }
    prob_densities = exp(probs)
    probs = t(apply(probs, 1, function(x) x-max(x)))
    probs = exp(probs)
    probs = probs/rowSums(probs)
    #determine new groups
    new_groups = apply(probs, 1, which.max)
    if (keep_initial_groups){
      data$group = ifelse(is.positive(initial_groups), initial_groups, new_groups)
    }
    else{
      data$group = new_groups
    }
    
    #final iteration is cluster-only (since I reversed the order of the E-M algorithm)
    if (i != n_iter + 1){
      
      #calculate new priors with smoothing
      if (!fix_priors){
        tab = as.numeric(table(data$group))
        priors = tab/sum(tab)
        priors = (priors + prior_smoothing_constant)/sum(priors + prior_smoothing_constant)
      }
      
      #calculate new loadings
      #numeric
      if (covariance_across_classes[1]=='constant'){
        covariance_matrix = mean.centered.covariance(data[,numeric_variables], data$group, covariance_constraint)
        for (g in 1:n_groups){
          subdata = data %>% filter(group==g)
          gmean[[g]] = as.numeric(colMeans(subdata[,numeric_variables]))
          names(gmean[[g]]) = numeric_variables
          gvar[[g]] = covariance_matrix
        }
        
      }
      #if unequal variance
      else{
        for (g in 1:n_groups){
          subdata = data %>% filter(group==g)
          gmean[[g]] = as.numeric(colMeans(subdata[,numeric_variables]))
          names(gmean[[g]]) = numeric_variables
          gvar[[g]] = constrained.covariance(subdata[,numeric_variables], covariance_constraint)
        }
      }
      #categorical estimates
      for (g in 1:n_groups){
        gclass[[g]] = all.class.estimates(data[,categorical_variables], lambda=class_smoothing_constant)
        if (length(interaction_varnames) > 0){
          gclass_interaction[[g]] = all.class.estimates(data[,interaction_varnames], lambda=class_interaction_smoothing_constant)
        }
        
      }
    }
    
    #record history
    if (record_history){
      if (include_classes_in_history){
        group_copy = data$group
      }
      else{
        group_copy=NULL
      }
      entry = list(classes = group_copy, mu = gmean, sigma = gvar, class_prop = gclass, class_prop_interaction = gclass_interaction,
                   priors = priors, prob_densities=prob_densities)
      history[[1+i]] = entry
    }
  }
  for (g in 1:n_groups){
    names(gmean[[g]]) = numeric_variables
    rownames(gvar[[g]]) = numeric_variables
    colnames(gvar[[g]]) = numeric_variables
  }
  if (include_data_copy)
    return(list(classes=data$group, probs = probs, prob_densities=prob_densities,
                mu=gmean, sigma=gvar, priors=priors, data=data,
                class_effects = gclass, class_interaction_effects = gclass_interaction,
                variables = list(
                numeric_variables = numeric_variables, categorical_variables=categorical_variables,
                interaction_class_variables=interaction_class_variables,
                interaction_varnames=interaction_varnames,
                variables=variables),
                n_groups=n_groups, history=history,
                unmodified_data=original_data,
                n_iter = n_iter))
  return(list(classes=data$group, probs = probs, prob_densities=prob_densities,
              mu=gmean, sigma=gvar, priors=priors,
              class_effects = gclass, class_interaction_effects = gclass_interaction,
              variables = list(
                numeric_variables = numeric_variables, categorical_variables=categorical_variables,
                interaction_class_variables=interaction_class_variables,
                interaction_varnames=interaction_varnames,
                variables=variables),
              n_groups=n_groups, history=history,
              n_iter = n_iter))
}

generative.deviance <- function(model, use_density=TRUE, epsilon=1e-14){
  if (use_density)
    return(-2 * sum ( log(pmax(epsilon, apply(model$prob_densities, 1, max)))))
  else
    return(-2 * sum ( log(apply(model$probs, 1, max))))
}

generative.classify <- function(model, data, type=c('class','probs')){
  #load parameters from model
  numeric_variables = model$variables$numeric_variables
  categorical_variables = model$variables$categorical_variables
  interaction_class_variables = model$variables$interaction_class_variables
  gvar = model$sigma
  gmean = model$mu
  gclass = model$class_effects 
  gclass_interaction = model$class_interaction_effects
  priors = model$priors
  
  #add interaction classes if necessary
  interaction_varnames = character(0)
  if (!is.null(interaction_class_variables)){
    for (pair in interaction_class_variables){
      new_varname = paste(pair, collapse=':')
      data[,new_varname] = factor(paste(as.character(data[,pair[1]]), 
                                        as.character(data[,pair[2]])),
                                  collapse=':')
      interaction_varnames = c(interaction_varnames, new_varname)
      #remove variables from pair
      categorical_variables = categorical_variables[!categorical_variables %in% pair]
    }
  }
  
  #calculate probs & groups
  n_groups = model$n_groups
  probs = matrix(nrow=nrow(data), ncol=n_groups, 0)
  for (g in 1:n_groups){
    #prior initialization
    probs[,g] = log(priors[g])
    #multivariate normal contribution
    if (length(numeric_variables) > 0)
      probs[,g] = probs[,g] + log(dmvnorm(data[,numeric_variables], mean=gmean[[g]], sigma = gvar[[g]]))
    #categorical contribution
    if (length(categorical_variables) > 0){
      probs[,g] = probs[,g] + calc.all.class.probabilities(data[,categorical_variables], gclass[[g]])
    }
    #interaction effects
    if (length(interaction_varnames) > 0){
      probs[,g] = probs[,g] + calc.all.class.probabilities(data[,interaction_varnames], gclass[[g]])
    }
  }
  probs = apply(probs, 1, function(x) x-max(x))
  probs = exp(probs)
  probs = probs/rowSums(probs)
  #determine new groups
  new_groups = apply(probs, 1, which.max)
  results = list()
  if ('class' %in% type)
    results[['class']] = new_groups
  if ('probs' %in% type)
    results[['probs']] = probs
  return(results)
}

create_history_frame <- function(model, iter=model$n_iter){
  
 history_frame = ldply(llply(model$history, function(x) x$classes), 
                       function(x, data) cbind(data, data.frame(group=x)), data=model$unmodified_data)
 history_frame$iteration = rep(0:(model$n_iter+1), each=nrow(model$data)) 
 
 history_frame = history_frame %>% filter((iteration) <= (iter+1))
 return(history_frame)
}

#takes a model and plots the points and ellipsoidsfor each cluster over time
base.animated.multiplot <- function(model, variables=model$variables$numeric_variables, 
                                    max_iter=model$n_iter+1,
                                    ...){
  molten.history = melt.history(model %>% create_history_frame(iter=max_iter), variables=variables, ...)
  molten.ellipses = melt.to.ellipses(model, variables=variables, max_iter=max_iter, ...)
  
  ggplot() + 
    geom_point(data=molten.history, aes(x=val1, y=val2, color=factor(group), frame=iteration)) +
    geom_polygon(data=molten.ellipses, aes(x=val1, y=val2, fill=factor(group), frame=iteration), 
                 alpha=0.5) +
    geom_path(data=molten.ellipses, aes(x=val1, y=val2, color=factor(group), frame=iteration),
              alpha=0.9)
    facet_grid(var2~var1, scales='free')
  
}

#a melting function that melts combinations of variables so that they can be plotted against each other
#using ggplot2
melt.history <- function(history, 
                         variables=names(history)[!names(history) %in% c('group','iteration')],
                         id.vars=c('group','iteration'),
                         ...){
  combinations = combn(variables, 2)
  n_combinations = ncol(combinations)
  data_list = list()
  for (i in 1:n_combinations){
    col1 = combinations[1,i]
    col2 = combinations[2,i]
    new_data = history %>% 
      transmute_(val1=col1, val2=col2, group='group', iteration='iteration') %>%
      mutate(var1=col1, var2=col2)
    data_list[[i]] = new_data
  }
  bind_rows(data_list) %>% mutate(var1=factor(var1, levels=variables),
                                  var2=factor(var2, levels=rev(variables)))
}

melt.to.ellipses <- function(model, variables=model$variables$numeric_variables,
                        n_sigma=1.96, group_var='group',
                        max_iter=model$n_iter+1, 
                        segments=51){
  history = model$history
  combinations = combn(variables, 2)
  n_combinations = ncol(combinations)
  data_list = list()
  for (i in 1:n_combinations){
    col1 = combinations[1,i]
    col2 = combinations[2,i]
    path = create_ellipsoid_paths_from_history(model, c(col1, col2),
                                               n_sigma=1.96, group_var='group', 
                                               max_iter = model$n_iter+1,
                                               segments=51)
    new_data = path %>% 
      transmute_(val1=col1, val2=col2, group='group', iteration='iteration') %>%
      mutate(var1=col1, var2=col2)
    data_list[[i]] = new_data
  }
   bind_rows(data_list) %>% mutate(var1=factor(var1, levels=variables),
                                   var2=factor(var2, levels=rev(variables)))
}



#useful for when the ellispoids are constrained in any way 

#stolen code from ggplot2:::calculate_ellipse
create.ellipse.path <- function(v, segments=51, n_sigma=1.96, variables=names(v$mu)[1:2], index=NULL,
                                group_var='group'){
  if (!is.null(index)){
    shape=v$sigma[[index]][variables, variables]
    center = v$mu[[index]][variables]
  }
  else{
    shape <- v$sigma[variables, variables]
    center <- v$mu[variables]
  }
  e.vals = sqrt(n_sigma * eigen(shape)$values)
  e.vecs = eigen(shape)$vectors
  angles <- (0:segments) * 2 * pi/segments
  base.ellipse <- cbind(cos(angles) * e.vals[2], sin(angles) * e.vals[1])
  #how the f\w{2}k is [,2:1] the solution to fixing the problem??? 
  ellipse <- as.data.frame(base.ellipse %*% (e.vecs[,2:1]))
  ellipse[,1] = ellipse[,1] + center[1]
  ellipse[,2] = ellipse[,2] + center[2]
  ellipse[,group_var] = index
  names(ellipse)[1:2] = variables
  return(ellipse)
}

create_ellipsoid_paths_from_history <- function(model, variables = model$variables$numeric_variables[1:2],
                                                n_sigma=1.96, group_var='group', max_iter = model$n_iter+1,
                                                segments=51){
  
  n_groups = model$n_groups
  history = model$history
  ellipsoid_list = list()
  for (i in 1:(max_iter + 1)){
    elem = history[[i]]
    ellipsoids = adply(1:n_groups, 1, create.ellipse.path, 
                       variables=variables, 
                       group_var=group_var, 
                       n_sigma=n_sigma,
                       segments=segments,
                       v=elem)
    ellipsoids$iteration = i-1
    ellipsoid_list[[i]] = ellipsoids
  }
  return(bind_rows(ellipsoid_list))
}


#ellipse_func <- function(x, variables, n_segments){
#  v1 = variables[1]
#  v2 = variables[2]
#  #v = data.frame(var1 = v1, var2=v2, mu1=x$mu[v1], mu2=x$mu[v2], sigma.sq_11=x$sigma[v1,v1], 
#  #           sigma.sq_22=x$sigma[v2,v2], sigma.sq_12=x$sigma[v1,v2])
#  v = list(sigma=x$sigma, mu=x$mu)
#  ellipse = create.ellipse.path(x, n_sigma=1,segments=segments)
#}