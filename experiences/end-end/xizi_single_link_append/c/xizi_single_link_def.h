typedef struct SingleLinklistNode
{
    struct SingleLinklistNode *node_next;
} SysSingleLinklistType;

/*@ Extern Coq (xizi_sll : Z -> list Z -> Assertion)
               (xizi_sllseg : Z -> Z -> list Z -> Assertion)
               (xizi_sll_head : Z -> list Z -> Assertion)
 */
/*@ Import Coq Require Import xizi_single_link_lib */
/*@ include strategies "xizi_single_link.strategies" */
