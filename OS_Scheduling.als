open util/ordering[Process] as PO
open util/ordering[Scheduler] as SO
let PositiveInt = { i : Int | i > 0 }

abstract sig Process {
  state: State,
  pid: PositiveInt,
  nextProcess: Process
}

enum State {
  RUNNING,
  READY,
  WAITING
}

sig Scheduler {
  running: lone Process,
  ready: set Process,
  waiting: set Process
}

fact chainRule{
  // Only one process can be running at a time
  one s: Scheduler | one s.running
  // A process can only be in one state at a time
  all p: Process | lone s: State | p.state = s
  //no two process will share same PID
  all p1, p2: Process | p1 != p2 => p1.pid != p2.pid
  // no process can be next of two processes
  all p1, p2: Process | p1 != p2 => p1.nextProcess != p2.nextProcess
  //one process can not be next of self
  all p: Process | p != p.nextProcess
  //no loop in process chain
 // no p: Process | p in (p.^nextProcess )
  //no p1, p2:Process | p1!=p2 => (p1.nextProcess = p2) and (p2.nextProcess = p1)
}

pred init[s: Scheduler] {
  // Initial state: no process is running, all processes are in the READY state
  no s.running and s.ready = Process and all p: Process | p.state = READY
}

pred readyToRunning[s, s": Scheduler] {
  // Transition: move a process from READY to RUNNING or change the running process state
  let selectedProcess = s.ready {
 	 one selectedProcess
 
	 s".running = selectedProcess
    	 s".ready = s.ready.nextProcess - selectedProcess
	 s".waiting = s.waiting 
	 s".running.state = RUNNING
  }

}

pred runningToReady[s, s": Scheduler] {
   let runningProcess = s.running {
	one runningProcess

	s".running = none 
	s".ready = s.ready + runningProcess 
	s".waiting = s.waiting 
	runningProcess.state = READY
   }
}

pred readyToWaiting[s,s": Scheduler] {
   let readyProcess = s.ready {
	one readyProcess

	s".ready = s.ready.nextProcess - readyProcess
	s".running = s.running 
	s".waiting = s.waiting + readyProcess
	readyProcess.state = WAITING
   }
}

pred waitingToReady[s,s":Scheduler] {
   let waitingProcess = s.waiting {
	one waitingProcess

	s".ready = s.ready + waitingProcess
	s".waiting = s.waiting.nextProcess - waitingProcess 
	s".running = s.running
	waitingProcess.state = READY
   }
}

pred runningToWaiting[s,s":Scheduler] {
   let runningProcess = s.running {
	one runningProcess

	s".ready = s.ready and
	s".waiting = s.waiting + runningProcess and
	s".running = none and 
	runningProcess.state = WAITING
   }
}

fact {
	// init
	SO/first.ready = PO/first
	PO/first.state = READY
	SO/first.ready.nextProcess = PO/first.next
	SO/first.waiting = none
	SO/first.running = none

	all s": Scheduler - first, s: s".prev {
		runningToReady[s,s"] 
	or
		readyToRunning[s,s"] 
	or
		waitingToReady[s,s"]
	or
		readyToWaiting[s,s"]
	or
		runningToWaiting[s,s"]
	}

}
