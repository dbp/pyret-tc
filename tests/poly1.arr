#lang pyret

#==

fun<T> f(a :: T, g :: (T -> T)) -> T:
  g(a)
end