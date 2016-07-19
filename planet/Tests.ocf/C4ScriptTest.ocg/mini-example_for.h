func Main(){
	var condition = false;
	for( Initialize() ; condition ; Step() )
		Body();
}

func Initialize(){}
func Step(){}
func Body(){}
