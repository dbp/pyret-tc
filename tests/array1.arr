#lang pyret

#==

x :: Array<String> = array-of("foo", 10)

fun s(a :: Array<String>) -> String:
  a.get(1)
end