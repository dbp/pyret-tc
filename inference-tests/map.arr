#lang pyret

fun add1(n):
  n + 1
where:
  add1(1) is 2
end

fun map(fn, l):
  cases(List) l:
    | empty => empty
    | link(f, r) => link(fn(f), map(fn, r))
  end
where:
  map(tostring, [1,2,3]) is ["1", "2", "3"]
  map(add1, [1]) is [2]
  map(tostring, [true]) is ["true"]
end