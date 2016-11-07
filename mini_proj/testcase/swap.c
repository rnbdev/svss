int main(){
    int x, y, c;
    __ASSUME(x == y);
    c = x;
    x = y;
    y = c;
    __ASSERT(x != y);
    return 0;
}