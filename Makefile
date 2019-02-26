all:
	-apt update -y
	-apt install curl -y
	-curl -sL https://deb.nodesource.com/setup_11.x | bash
	-apt install -y nodejs
	-apt install -y minisat