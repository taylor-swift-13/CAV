#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

void xizi_single_link_init(SysSingleLinklistType *linklist)
/*@ With first
    Require
      linklist != 0 &&
      linklist -> node_next == first
    Ensure
      linklist -> node_next == 0 &&
      xizi_sll(0, nil)
*/
{
    linklist->node_next = (void *)0;
}
