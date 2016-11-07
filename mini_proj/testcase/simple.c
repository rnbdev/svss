int main(){
    int x, y;
    __ASSUME(x > 0);
    y = x;
    y = x + 2;
    if(y > 0){
        y = y - 1;
        if(y == 0){
            __ASSERT(y != 0);
        }
    }
    return 0;
}
