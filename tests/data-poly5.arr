#lang pyret

#==

fun<T> foo(x :: Option<T>) -> T:
  cases(Option<T>) x:
    | none => raise("Fail")
    | some(w) => w
  end
end