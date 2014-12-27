########################################################################################
##   Julian Sia's Implementation of sum product (belief propogation) and max product  ## 
##   algorithms in R (for binary trees and binary random variables) in fulfilmment of ## 
##   Problem Set 2 of Professor Ravikumar's C S 395T Graphical Models                 ##
########################################################################################


# Functions for sumProduct algorithm
nodeMake <- function() {  
  return (data.frame(currBelief=c(0,0),
               leftReceive=c(0,0),
               rightReceive=c(0,0),
               parentReceive=c(0,0)))
}

levelCount <- function(nodes) {
  levels = 0
  count = 0
  while(count < nodes) {
    count = count + 2^levels
    levels = levels + 1
  }
  return(levels)
}

initTree <- function(levels) {
  nodes = 0
  for (i in (levels-1):0) {
    nodes = nodes + 2^i
  }
  tree = list()
  for(i in 1:nodes) {
    curr = nodeMake()
    tree[[i]] = curr
  }
  return (tree)
}

sumProd <- function(left, right) {
  i = 1
  temp = c()
  for (l in left) {
    for (r in right) {
      temp[i] = l*r
      i = i + 1
    }
  }
  
  top = temp[1:((length(temp)/2))]
  bottom = temp[((length(temp)/2 + 1)):((length(temp)))]
  
  result = c(sum(top), sum(bottom))
  return(result)
}

messageUp <- function(tree, left_potential, right_potential, root_potential) {
  # assume tree's nodes are init to [1,1]
  
  # left_potential = c(.7,.3)
  # right_potential = c(.6,.4)
  # root_potential = c(.1,.9)
  
  for (i in length(tree):1) {
    # node is right mod 2 is 0, else left
    
	# root
    if(i == 1) {
      curr_left = tree[[i]]["leftReceive"]
      curr_right = tree[[i]]["rightReceive"]
      temp = sumProd(curr_left[[1]], curr_right[[1]])
      tree[[1]]["currBelief"] = c(sum(temp)*root_potential[1], sum(temp)*root_potential[2])
    }
    
	# leaves
    if (i %% 2 == 1 & all(tree[[i]]["rightReceive"] == c(0,0))) {
      # message right's parent
      tree[[i]]["currBelief"] = right_potential
      tree[[trunc(i/2)]]["rightReceive"] = right_potential
    } else if (i %% 2 == 0 & all(tree[[i]]["leftReceive"] == c(0,0))) {
      tree[[i]]["currBelief"] = left_potential
      tree[[trunc(i/2)]]["leftReceive"] = left_potential
    } 
	
	# non-leaves
	if (i != 1 & all(tree[[i]]["rightReceive"] != c(0,0)) & all(tree[[i]]["leftReceive"] != c(0,0))) {
      curr_left = tree[[i]]["leftReceive"]
      curr_right = tree[[i]]["rightReceive"]
      
	  if(i %% 2 == 1) {
	  	temp = sumProd(curr_right[[1]], curr_left[[1]])
		  tree[[i]]["currBelief"] = sumProd(temp, left_potential)  
	  } else {
	  	temp = sumProd(curr_left[[1]], curr_right[[1]])
		  tree[[i]]["currBelief"] = sumProd(temp, right_potential)   
	  }
	  
	  if(i > 1) {
      	if(i %% 2 == 1) {
          tree[[trunc(i/2)]]["rightReceive"] = tree[[i]]["currBelief"]
     	} else {
      	  tree[[trunc(i/2)]]["leftReceive"] = tree[[i]]["currBelief"]
	  	}
  	  }
  	} 
  }
  
  return(tree)
}

messageDown <-function(tree) {
  for (i in 1:length(tree)) {
    if (i != 1) {
      # update beliefs if not root
      p_1 = sum(tree[[i]]["currBelief"]*tree[[i]]["parentReceive"])
      p_0 = 1-p_1
      tree[[i]]["currBelief"] = c(p_1, p_0)                
    }
    
    if (2*i <= length(tree)) {
      tree[[2*i]]["parentReceive"] = tree[[i]]["currBelief"]
      tree[[(2*i)+1]]["parentReceive"] = tree[[i]]["currBelief"]
    }
  }
  return(tree)
}

inferSumProdTreeBinary <- function(levels, left, right, root) {
	tree = initTree(levels)
	tree_up = messageUp(tree, left, right, root)
	tree_down = messageDown(tree_up)
	return(tree_down)
}

#################################################################################
#################################################################################


# Functions for maxProduct
maxNodeMake <- function() {  
  return (c(currBelief=0,
               leftReceive=0,
               rightReceive=0))
}

# Initialize a binary tree with "levels levels"
initMaxTree <- function(levels) {
  nodes = 0
  for (i in (levels-1):0) {
    nodes = nodes + 2^i
  }
  tree = list()
  for(i in 1:nodes) {
    curr = maxNodeMake()
    tree[[i]] = curr
  }
  return (tree)
}

# propogate the children's probabilities upwards through the tree
maxMessageUp <- function(tree, left_potential, right_potential, root_potential) {
  
  # left_potential = c(.7,.3)
  # right_potential = c(.6,.4)
  # root_potential = c(.1,.9)
  
  terminating_index = -1
  equal_roots = 0
  
  choices = rep(-1, length(tree))
  
  for (i in length(tree):1) {
    
    curr_left = tree[[i]]["leftReceive"]
    curr_right = tree[[i]]["rightReceive"]
    
    # if a leaf
    if (i > 1 & all(curr_left == 0 & curr_right == 0)) {
      if (i %% 2 == 1) {
        tree[[i]]["currBelief"] = max(right_potential)
        tree[[trunc(i/2)]]["rightReceive"] = tree[[i]]["currBelief"]
        choices[i] = which.max(right_potential)
      } else {
        tree[[i]]["currBelief"] = max(left_potential)
        tree[[trunc(i/2)]]["leftReceive"] = tree[[i]]["currBelief"]
        choices[i] = which.max(left_potential)
      }
    }

    # not leaf, not root
    if (i > 1 & all(curr_left != 0 & curr_right != 0)){
      if (i %% 2 == 1) {
        tree[[i]]["currBelief"] = max(curr_left * curr_right * right_potential)
        tree[[trunc(i/2)]]["rightReceive"] = tree[[i]]["currBelief"]
        choices[i] = which.max(curr_left * curr_right * right_potential)
      } else {
        tree[[i]]["currBelief"] = max(curr_left * curr_right * left_potential)
        tree[[trunc(i/2)]]["leftReceive"] = tree[[i]]["currBelief"]
        choices[i] = which.max(curr_left * curr_right * left_potential)
      }
    }
    
    # root
    if (i == 1) {
      if(root_potential[1] == root_potential[2]) {
        equal_roots = 1
      }
      tree[[i]]["currBelief"] = max(curr_left * curr_right * root_potential)
      terminating_index = which.max(curr_left * curr_right * root_potential)
      choices[i] = which.max(curr_left * curr_right * root_potential)
    }
  }
  
  # if the terminating_index is 2 (ie, corresopnding to X=0, then the semantics of the indices change)
  # if terminating_index == 1 (the root), then the semantics of 1 --> P(left = 1 | parent = 1)
  # if terminating_index == 1 (the root), then the semantics of 2 --> P(left = 0 | parent = 1)
  # if terminating_index == 2 (the root), then the semantics of 2 --> P(left = 0 | parent = 0)
  # if terminating_index == 2 (the root), then the semantics of 1 --> P(left = 1 | parent = 0)
  if (terminating_index == 2) {
    for (i in 2:length(choices)) {
      if(choices[i] == 1) {
        choices[i] = 2
      } else {
        choices[i] = 1
      }
    }
  }
  
  if (equal_roots == 1) {
    # in the case of an equal probability, we find that there are two probability maximizing configus
    return(list(choices, 2*choices))
  }
  return(choices)
}

# generate a binary tree of "levels" levels with distributions defined by 
# lists of left, right, and root, which describe binary outcomes 
# e.g., left =  c(.7,.3)
inferMaxProduct <- function(levels, left, right, root) {
  tree = initMaxTree(levels)
  max_mup = maxMessageUp(tree, left, right, root)
  return(max_mup)
}



