func log2( s1 , s2 ){
	Log("%v:%v", s1, s2);
}

func Main(){
	for( var a in [0, 1, 1, 2, 3, 5, 8, 11, 19, 30, 49] )
	{
		if( a == 3 )
			continue;
		for( var s in [99, 98, 97] )
		{
			if( a == 8 )
				continue;
			log2(a,s);
			if( a == 11 )
				break;
		}
		if( a == 30 )
			break;
	}
}