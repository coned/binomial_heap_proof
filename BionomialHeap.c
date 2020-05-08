#include <stdio.h>
#include <stdlib.h>
const int MAX_INF = 199999;

typedef struct node_t {
    int value;
	int degree;
	struct node_t *child;
	struct node_t *parent;
	struct node_t *brother;
} node;

typedef struct heap_t {
    node* head;
} heap;

node* node_init(int v) {
	node* n = malloc(sizeof(node));
	n->value = v;
	n->degree = 0;
    n->child = NULL;
    n->parent = NULL;
    n->brother = NULL;
	return n;
}

heap* heap_init() {
    heap* h = malloc(sizeof(heap));
    h->head = NULL;
    return h;
}

void combine_tree(node *p, node *c) { // c must be the child of p
    c->parent = p;
    c->brother = p->child;
    p->child = c;

    p->degree += 1;
}

node* combine_tree_short(node* n1, node* n2) {
    if (n1->value < n2->value) {
        combine_tree(n1, n2);
        return n1;
    } else {
        combine_tree(n2, n1);
        return n2;
    }
}

heap* merge(heap* h1, heap* h2) {
    heap *h = heap_init();
    if(h1->head == NULL) {h->head = h2->head; return h;}
    if(h2->head == NULL) {h->head = h1->head; return h;}

    node **tail = &(h->head);
    node *p = NULL;

    while (h1->head != NULL && h2->head != NULL) {
        if (p == NULL) {
            if (h1->head->degree == h2->head->degree) {
                node *a = h1->head, *b = h2->head;
                h1->head = h1->head->brother;
                h2->head = h2->head->brother;
                p = combine_tree_short(a, b);
            } else {
                if(h1->head->degree < h2->head->degree) {
                    *tail = h1->head;
                    tail = &((*tail)->brother);
                    h1->head = h1->head->brother;
                } else {
                    *tail = h2->head;
                    tail = &((*tail)->brother);
                    h2->head = h2->head->brother;
                }
            }
        } else {
            if (h1->head->degree == h2->head->degree) {
                *tail = p;
                tail = &((*tail)->brother);
                node *a = h1->head, *b = h2->head;
                h1->head = h1->head->brother;
                h2->head = h2->head->brother;
                p = combine_tree_short(a, b);
            } else {
                if (h1->head->degree == p->degree) {
                    node *a = h1->head;
                    h1->head = h1->head->brother;
                    p = combine_tree_short(a, p);
                } else if (h2->head->degree == p->degree) {
                    node *b = h2->head;
                    h2->head = h2->head->brother;
                    p = combine_tree_short(b, p);
                } else {
                    *tail = p;
                    tail = &((*tail)->brother);
                    p = NULL;
                }
            }
        }
    }

    

    if(h1->head == NULL) {
        while(p != NULL && h2->head != NULL) {
            if (p->degree == h2->head->degree) {
                node *b = h2->head;
                h2->head = h2->head->brother;
                p = combine_tree_short(p, b);
            } else {
                *tail = p;
                tail = &((*tail)->brother);
                p = NULL;
            }
        }
        *tail = h2->head;
    }
    if(h2->head == NULL) {
        while(p != NULL && h1->head != NULL) {
            if (p->degree == h1->head->degree) {
                node *b = h1->head;
                h1->head = h1->head->brother;
                p = combine_tree_short(p, b);
            } else {
                *tail = p;
                tail = &((*tail)->brother);
                p = NULL;
            }
        }
        *tail = h1->head;
    }

    if(p != NULL) {
        *tail = p;
        tail = &((*tail)->brother);
    }
    // if(h1->head->degree <= h2->head->degree) {
    //     h->head = h1->head;
    //     h1->head = h1->head->brother;
    // } else {
    //     h->head = h2->head;
    //     h2->head = h2->head->brother;
    // }
    // now = h->head;
    // node* prev = NULL;
    // while(now->brother != NULL) {
    //     if (now->degree == now->brother->degree) {
    //         if (now->value < now->brother->value) {
    //             node* tmp = now->brother->brother;
    //             combine_tree(now, now->brother);
    //             now->brother = tmp;
    //         } else {
    //             if (prev == NULL) {
    //                 h->head = now->brother;
    //                 combine_tree(now->brother, now);
    //                 now = h->head;
    //             } else {
    //                 prev->brother = now->brother;
    //                 combine_tree(now->brother, now);
    //                 now = prev->brother;
    //             }
    //         }
    //     } else {
    //         prev = now;
    //         now = now->brother;
    //     }
    // }

    return h;
}

heap* insert(heap* h, int value) {
    node* n = node_init(value);
    heap* h1 = heap_init();
    h1->head = n;
    heap* h2 = merge(h, h1);
    free(h1);
    free(h);
    return h2;
}

int get_min(heap* h) {
    int min_value = MAX_INF;
    if (h->head == NULL) return min_value;

    node* now = h->head;
    while (now != NULL) {
        if (min_value > now->value) min_value = now->value;
        now = now->brother;
    }

    return min_value;
}

heap* del_min(heap* h) {
    int min_value = MAX_INF;
    node* min_pos = NULL;
    node* min_prev = NULL;
    if (h->head == NULL) {
        free(h);
        return heap_init();
    }

    node* now = h->head;
    node* prev = NULL;
    while (now != NULL) {
        if (min_value > now->value) {
            min_value = now->value;
            min_pos = now;
            min_prev = prev;
        }
        prev = now;
        now = now->brother;
    }

    if(min_prev == NULL) {
        h->head = h->head->brother;
    } else {
        min_prev->brother = min_pos->brother;
    }
    

    heap* h1 = heap_init();
    while (min_pos->child != NULL) {
        node* c = min_pos->child;
        min_pos->child = c->brother;
        c->parent = NULL;
        c->brother = h1->head;
        h1->head = c;
    }
    free(min_pos);

    heap* h2 = merge(h, h1);
    free(h1);
    free(h);
    return h2;
}

void free_node(node* n) {
    if(n->child != NULL) free_node(n->child);
    if(n->brother != NULL) free_node(n->brother);
    free(n); 
}

void free_heap(heap* h) {
    if(h->head != NULL) free_node(h->head);
    free(h);
}

void print_heap(heap* h) {
    node* n = h->head;
    printf("heap:");
    while(n != NULL) {
        printf("%d ", n->value);
        n = n->brother;
    }
    printf("\n");
}

int main () {
    heap* h = heap_init();
    h = insert(h, 5);
    //print_heap(h);
    h = insert(h, 10);
    //print_heap(h);
    h = insert(h, 15);
    //print_heap(h);
    h = insert(h, 3);
    //print_heap(h);
    h = del_min(h);
    h = insert(h, 7);
    //print_heap(h);
    h = del_min(h);
    h = insert(h, 8);
    //print_heap(h);
    printf("%d\n", get_min(h));

    free_heap(h);
    return 0;
}