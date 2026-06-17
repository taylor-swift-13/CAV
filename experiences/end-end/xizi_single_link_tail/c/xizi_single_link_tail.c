#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

SysSingleLinklistType *xizi_single_link_tail(SysSingleLinklistType *linklist)
/*@ With l
    Require
      linklist != 0 &&
      xizi_sll(linklist, l)
    Ensure
      exists l1 d,
        l == app(l1, cons(d, nil)) &&
        __return != 0 &&
        xizi_sllseg(linklist@pre, __return, l1) *
        (__return -> node_next == 0)
*/
{
    /*@ Inv
          exists l1 d l2 next,
            l == app(l1, cons(d, l2)) &&
            linklist != 0 &&
            linklist -> node_next == next &&
            xizi_sllseg(linklist@pre, linklist, l1) *
            xizi_sll(next, l2)
    */
    while (linklist->node_next) {
        linklist = linklist->node_next;
    }

    return linklist;
}
