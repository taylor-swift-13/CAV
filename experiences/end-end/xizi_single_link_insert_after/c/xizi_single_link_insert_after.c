#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

void xizi_single_link_insert_after(SysSingleLinklistType *linklist, SysSingleLinklistType *linklist_node)
/*@ With first l old_next
    Require
      linklist != 0 &&
      linklist_node != 0 &&
      linklist -> node_next == first &&
      xizi_sll(first, l) &&
      linklist_node -> node_next == old_next
    Ensure
      linklist -> node_next == linklist_node &&
      xizi_sll(linklist_node, cons(0, l))
*/
{
    linklist_node->node_next = linklist->node_next;
    linklist->node_next = linklist_node;
}
