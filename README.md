# Overview

The code in `generative_model.r` contains a few primary functions that are very useful for general purposes:

`generative_model` -  This function runs a generative model on a data set, using a combination of numeric and/or categorical variables, with unsupervised, semi-supervised, and supervised modes, depending on the parameters provided and the data set supplied. Its history can be recorded, which allows you to visualize each iteration of its learning.

`generative.deviance` - This function evaluates the cohesiveness of the model in terms of deviance. Out-of-cluster deviance needs to be implemented to get a good idea of goodness-of-fit for the data.

`generative.classify` - This takes a model generated by `generative_model` and a data set, and then performs classifies the clusters of the data set based on the model's parameters.

`base.animated.multiplot` - This function creates an animated plot of a model's clustering progress over time. If you are on Windows, you may need to install `animation` from my forked repo if your ImageMagick location is in a directory containing a space.

`melt.history` - A function that expands the clustering/classification history of all the points from a model.

# blog link

Here is a blog post using this code (and made by the .Rhtml file): [http://maxcandocia.com/article/2018/Jan/09/generative-clustering/](http://maxcandocia.com/article/2018/Jan/09/generative-clustering/)