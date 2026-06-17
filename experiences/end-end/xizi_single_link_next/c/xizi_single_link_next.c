#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

SysSingleLinklistType *xizi_single_link_next(SysSingleLinklistType *linklist_node)
/*@ With next l
    Require
      linklist_node != 0 &&
      (linklist_node -> node_next == next) *
      xizi_sll(next, l)
    Ensure
      __return == next &&
      (linklist_node -> node_next == next) *
      xizi_sll(next, l)
*/
{
    return linklist_node->node_next;
}
