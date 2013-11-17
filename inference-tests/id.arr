#lang pyret

fun id(x):
  x
where:
  id(10) is 10
  id(true) is true
end