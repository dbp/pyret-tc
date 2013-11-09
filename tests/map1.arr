#lang pyret

fun my-map(fn :: (Any -> Any), l :: List<Any>) -> List<Any>:
  cases(List<Any>) l:
    | empty => empty
    | link(f,r) => link(fn(f),my-map(fn, r))
  end
end
my-map(fun(x): x+1 end, [1,2,3])
