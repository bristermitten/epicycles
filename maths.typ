Bidirectional stuff


Lens laws - for some lens $l$: 
-  Get: `view l (set l v s) = v`
- Put: `set l (view l s) s = s`

For some function $f(x, y) = z$ 
- Forward: $f(x, y) = z$
- Backward: $f(x', y') = z'$, so we want to find $Delta x, Delta y$ such that $f(x + Delta x, y + Delta y) = z'$
  - aim to 