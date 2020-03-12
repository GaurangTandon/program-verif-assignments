#include <cstdio>
#include <assert.h>
#include <iostream>
using namespace std;
#include "vops.h"
#include "linkedlist.h"
namespace ANONYMOUS{

Node* Node::create(Node*  next_, int  val_){
  void* temp= malloc( sizeof(Node)  ); 
  Node* rv = new (temp)Node();
  rv->next =  next_;
  rv->val =  val_;
  return rv;
}
List* List::create(Node*  head_){
  void* temp= malloc( sizeof(List)  ); 
  List* rv = new (temp)List();
  rv->head =  head_;
  return rv;
}
void testInsert__Wrapper() {
  testInsert();
}
void testInsert__WrapperNospec() {}
void testAppend__Wrapper() {
  testAppend();
}
void testAppend__WrapperNospec() {}
void testInsert() {
  List*  l=List::create(NULL);
  List*  l_s4=NULL;
  populate(l, l_s4);
  Node*  n1=Node::create(NULL, 70);
  List*  l2_s6=NULL;
  insertAt(l_s4, n1, 1, l2_s6);
  assert ((l2_s6->head->next->val) == (70));;
}
void testAppend() {
  List*  l=List::create(NULL);
  List*  l_s8=NULL;
  populate(l, l_s8);
  Node*  n1=Node::create(NULL, 40);
  List*  l1_s10=NULL;
  append(l_s8, n1, l1_s10);
  assert ((l1_s10->head->next->next->val) == (40));;
}
void populate(List* l, List*& _out) {
  Node*  n2=Node::create(NULL, 60);
  Node*  n1=Node::create(n2, 5);
  l->head = n1;
  _out = l;
  return;
}
void insertAt(List* lst, Node* n, int pos_0, List*& _out) {
  int  pos=pos_0;
  Node*  head=NULL;
  head = lst->head;
  if ((pos_0) == (0)) {
    n->next = head;
    lst->head = n;
    _out = lst;
    return;
  }
  assert ((head) != (NULL));;
  pos = pos_0 - 1;
  while ((pos) > (0)) {
    pos = pos - 1;
    assert ((head) != (NULL));;
    head = head->next;
  }
  n->next = head->next;
  head->next = n;
  _out = lst;
  return;
}
void append(List* lst, Node* n, List*& _out) {
  Node*  head=NULL;
  head = lst->head;
  if ((head) == (NULL)) {
    lst->head = n;
    _out = lst;
    return;
  }
  bool  __sa0=(head->next) != (NULL);
  while (__sa0) {
    head = head->next;
    __sa0 = (head->next) != (NULL);
  }
  head->next = n;
  _out = lst;
  return;
}

}
