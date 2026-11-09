import sys; sys.path.insert(0,'tools')
import eps1_chain as C
from eps1_chain import NUM, ATOM, ATOM1
ch=[NUM(1),NUM(2)]
print('val', C.val(ch), 'full', C.full(0,ch))
print('pred', C.pred_chain(ch), 'val', C.val(C.pred_chain(ch)))
print('step', C.step(0,ch,3))
