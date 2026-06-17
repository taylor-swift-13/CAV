#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

void xizi_single_link_append(SysSingleLinklistType *linklist, SysSingleLinklistType *linklist_node)
/*@ With l old_next
    Require
      linklist != 0 &&
      linklist_node != 0 &&
      xizi_sll(linklist, l) &&
      linklist_node -> node_next == old_next
    Ensure
      xizi_sll(linklist, app(l, cons(0, nil)))
*/
{
    struct SingleLinklistNode *node;

    node = linklist;

    /*@ Inv
          exists l1a d l1b next,
            l == app(l1a, cons(d, l1b)) &&
            linklist == linklist@pre &&
            linklist_node == linklist_node@pre &&
            node != 0 &&
            node -> node_next == next &&
            xizi_sllseg(linklist, node, l1a) *
            xizi_sll(next, l1b) &&
            linklist_node -> node_next == old_next
    */
    while (node->node_next) {
        node = node->node_next;
    }

    node->node_next = linklist_node;
    linklist_node->node_next = (void *)0;
}
