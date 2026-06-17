#include "verification_stdlib.h"
#include "verification_list.h"
#include "xizi_single_link_def.h"

SysSingleLinklistType *xizi_single_link_remove_node(SysSingleLinklistType *linklist, SysSingleLinklistType *linklist_node)
/*@ With l_before l_after target_next
    Require
      linklist != 0 &&
      linklist_node != 0 &&
      linklist != linklist_node &&
      xizi_sll_to_target(linklist, linklist_node, l_before) *
      (linklist_node -> node_next == target_next) *
      xizi_sll(target_next, l_after)
    Ensure
      __return == linklist &&
      linklist_node -> node_next == target_next &&
      xizi_sll(linklist, app(l_before, l_after))
*/
{
    struct SingleLinklistNode *node = linklist;

    /*@ Inv
          exists l1 d l2 next,
            l_before == app(l1, cons(d, l2)) &&
            linklist == linklist@pre &&
            linklist_node == linklist_node@pre &&
            node != 0 &&
            node -> node_next == next &&
            xizi_sllseg(linklist, node, l1) *
            xizi_sll_to_target(next, linklist_node, l2) *
            (linklist_node -> node_next == target_next) *
            xizi_sll(target_next, l_after)
    */
    while (node->node_next && node->node_next != linklist_node) {
        node = node->node_next;
    }

    /*@ Assert
          exists l1 d,
            l_before == app(l1, cons(d, nil)) &&
            linklist == linklist@pre &&
            linklist_node == linklist_node@pre &&
            linklist_node != 0 &&
            node != 0 &&
            node -> node_next == linklist_node &&
            xizi_sllseg(linklist, node, l1) *
            (linklist_node -> node_next == target_next) *
            xizi_sll(target_next, l_after)
    */
    if (node->node_next != (SysSingleLinklistType *)0) {
        node->node_next = node->node_next->node_next;
    }

    return linklist;
}
