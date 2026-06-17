#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

unsigned int xizi_single_link_len(const SysSingleLinklistType *linklist)
/*@ With first l
    Require
      linklist != 0 &&
      Zlength(l) <= UINT_MAX &&
      linklist -> node_next == first &&
      xizi_sll(first, l)
    Ensure
      __return == Zlength(l) &&
      linklist -> node_next == first &&
      xizi_sll(first, l)
*/
{
    unsigned int length = 0;
    const SysSingleLinklistType *tmp_list = linklist->node_next;

    /*@ Inv
          exists l1 l2,
            l == app(l1, l2) &&
            length == Zlength(l1) &&
            linklist == linklist@pre &&
            linklist -> node_next == first &&
            xizi_sllseg(first, tmp_list, l1) *
            xizi_sll(tmp_list, l2)
    */
    while (tmp_list != (void *)0)
    {
        tmp_list = tmp_list->node_next;
        length ++;
    }

    return length;
}
