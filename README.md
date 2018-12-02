# Idris-Blockchain

ProcessLib as per Ch. 15 of Brady's Type-Driven Development with Idris

Currently requires the package at https://github.com/idris-hackers/idris-crypto

To start Idris REPL, type:
idris -p contrib BlockchainMain.idris

To start simple blockchain simulation, type in Idris REPL:

:exec runProc (procMain [])

	Supported user commands:
	add str - add a block whose data field is str to the blockchain
	display - display the fields of the blocks of the current blockchain
	quit
	
To start distributed blockchain simulation with n "users" in private network,
type in n instances of the Idris REPL:

:exec runProc (procMain [p1,p2,...,pn])

where p1 is the port number of the current user and p2...pn are the port numbers
of the remaining (n-1) users

	Supported user commands:
	add str - Requires other users to input "receive" commands
	display
	quit
	receive - Required to recieve messages from other users
	rock/paper/scissors val - Smart Contracts used to play a RPS game between 2 distinct users; val used to obfuscate play of first player
	
