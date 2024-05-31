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

fun allProcessOfScheduler[s: Scheduler] : set Process {
	s.running + s.waiting + s.ready
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

  //one process can be in only one scheduler
  no p: Process, s1, s2: Scheduler | s1 != s2 and  p in allProcessOfScheduler[s1] and p in allProcessOfScheduler[s2]
  
  //processes in running will always have state RUNNING, same goes for other states
  all p: Process | p in Scheduler.running => p.state = RUNNING and p in Scheduler.waiting => p.state = WAITING and p in Scheduler.ready => p.state = READY
  
  //no loop in process chain
 // no p: Process | p in (p.^nextProcess )
  //no p1, p2:Process | p1!=p2 => (p1.nextProcess = p2) and (p2.nextProcess = p1)
}

pred init[s: Scheduler] {
  // Initial state: no process is running, all processes are in the READY state
  no s.running and s.ready = Process and all p: Process | p.state = READY
}
// ---------------------------- //
pred readyToRunning[s, s": Scheduler] {
  // Transition: move a process from READY to RUNNING or change the running process state
  let selectedProcess = s.ready {
 	 one selectedProcess
	 s".running.state = RUNNING
 
	 s".running = selectedProcess
    	 s".ready = s.ready.nextProcess - selectedProcess
	 s".waiting = s.waiting 
  }

}

pred runningToReady[s, s": Scheduler] {
   let runningProcess = s.running {
	one runningProcess
	runningProcess.state = READY

	s".running = none 
	//s".ready = s.ready + runningProcess 
	s".ready.nextProcess = runningProcess
	s".waiting = s.waiting 
   }
}

pred readyToWaiting[s,s": Scheduler] {
   let readyProcess = s.ready {
	one readyProcess
	readyProcess.state = WAITING

	s".ready = s.ready.nextProcess - readyProcess
	s".running = s.running 
	//s".waiting = s.waiting + readyProcess
	s".waiting.nextProcess = readyProcess
   }
}

pred waitingToReady[s,s":Scheduler] {
   let waitingProcess = s.waiting {
	one waitingProcess
	
	waitingProcess.state = READY

	//s".ready = s.ready + waitingProcess
	s".ready.nextProcess = waitingProcess
	s".waiting = s.waiting.nextProcess - waitingProcess 
	s".running = s.running
   }
}

pred runningToWaiting[s,s":Scheduler] {
   let runningProcess = s.running {
	one runningProcess
	runningProcess.state = WAITING

	s".ready = s.ready 
	//s".waiting = s.waiting + runningProcess and
	s".waiting.nextProcess = runningProcess
	s".running = none  
   }
}

fact {
	// init
	SO/first.ready = PO/first
	PO/first.state = READY
	SO/first.ready.nextProcess = PO/first.next
	SO/first.waiting = Process - (PO/first + PO/first.next)
	SO/first.running = none

//	all s": Scheduler - first, s: s".prev {
//		runningToReady[s,s"] 
//	or
//		readyToRunning[s,s"] 
//	or
//		waitingToReady[s,s"]
//	or
//		readyToWaiting[s,s"]
//	or
//		runningToWaiting[s,s"]
//	}

}
