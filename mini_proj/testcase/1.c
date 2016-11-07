int main(){
	int x;
	__ASSUME(x < 5);
	if(x < 5){
		x = x + 1;
	}
	__ASSERT(x <= 5);
}