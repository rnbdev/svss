int main(){
    int x, y, z;
    if(x > y){
        z = x;
    }else{
        z = y;
    }
    __ASSERT(z >= x, z >= y);
}