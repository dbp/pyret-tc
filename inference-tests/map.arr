#lang pyret

fun add1(n):
  n + 1
where:
  add1(1) is 2
end

fun bool2string(b):
  tostring(b)
where:
  bool2string(true) is "true"
end

fun map(fn, l):
  cases(List) l:
    | empty => empty
    | link(f, r) => link(fn(f), map(fn, r))
  end
where:
  map(add1, [1]) is [2]
  map(bool2string, [true]) is ["true"]
end