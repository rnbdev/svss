int main(){
    int y;
    __ASSUME(y > 50);
    if(y > 0){
        y = y+1;
    }else{
        y=y+3;
    }
    if(y>1){
        y = y+1;
    }
    __ASSERT(y > 20);
    return 0;
}