#lang pyret

#==

x :: List<Number> = [1,2,3].partition(fun(y :: Number): y < 2 end).is-true