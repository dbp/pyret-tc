#lang pyret

x :: List = [1,2,3].partition(fun(x :: Number): x < 2 end).is-true