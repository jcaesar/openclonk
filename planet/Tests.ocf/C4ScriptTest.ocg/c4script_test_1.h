func log(s) {
	Log("%v",s);
}

func Main() {
	for( var a = 39 ; a < 42 ; a = a+1 ){
		if( a == 40 )
			continue;
		log(a);
	}
}
