#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

SysSingleLinklistType *xizi_single_link_first(SysSingleLinklistType *linklist)
/*@ With first l
    Require
      linklist != 0 &&
      (linklist -> node_next == first) *
      xizi_sll(first, l)
    Ensure
      __return == first &&
      (linklist -> node_next == first) *
      xizi_sll(first, l)
*/
{
    return linklist->node_next;
}
