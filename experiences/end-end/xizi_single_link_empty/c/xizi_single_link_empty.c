#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

int xizi_single_link_empty(SysSingleLinklistType *linklist)
/*@ With first l
    Require
      linklist != 0 &&
      linklist -> node_next == first &&
      xizi_sll(first, l)
    Ensure
      (first == 0 => __return == 1) &&
      (first != 0 => __return == 0) &&
      linklist -> node_next == first &&
      xizi_sll(first, l)
*/
{
    return linklist->node_next == (void *)0;
}
