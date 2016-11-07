int main(){
  int x, y;
  __ASSUME(x >= 2);
  x = x + 2;
  __ASSERT(x > 3);
  return 0;
}
