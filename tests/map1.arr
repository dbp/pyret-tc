#lang pyret

A = Any
B = Any
List = list.List
empty = list.empty
link = list.link

fun my-map(fn :: (A -> B), l :: List<A>) -> List<B>:
  cases(List) l:
    | empty => empty
    | link(f,r) => link(fn(f),my-map(fn, r))
  end
end
my-map(fun(x): x+1 end, [1,2,3])
