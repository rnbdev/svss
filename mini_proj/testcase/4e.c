int main(){
	int x;
	__ASSUME(5 <= x); // equals to WP
	if(5 <= x){
		x = 5;
	}else{
		x = 4;
	}
	__ASSERT(5 <= x); // not equals to SP
	return 0;
}