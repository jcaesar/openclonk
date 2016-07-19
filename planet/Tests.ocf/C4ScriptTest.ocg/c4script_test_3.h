// Logging function
func log2( s1 , s2 ){
	Log("%v:%v", s1, s2);
}

// Will Compute the greatest common divisor
func ggT( a , b )
{
	while( b != 0 )
	{
		var tmp = a;
		if(a < b){
			// Swap a and b
			a = b;
			b = tmp;
			continue;
		}
		
		log2(a, b);
		
		// Do another iteration step
		a = b;
		b = tmp % b;
	}
	return a;
}


func Main(){
	Log("ggT: %v",ggT( 136681062 , 18632628 ));
}