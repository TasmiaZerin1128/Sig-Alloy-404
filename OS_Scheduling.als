open util/ordering[Process] as PO
open util/ordering[Scheduler] as SO
let PositiveInt = { i : Int | i > 0 }

abstract sig Process {
  state: State,
  pid: PositiveInt,
  nextProcess: Process,
  priority: PositiveInt
}

enum State {
  RUNNING,
  READY,
  BLOCKED
}

sig Scheduler {
  running: lone Process,
  ready: set Process,
  blocked: set Process
}

fun allProcessOfScheduler[s: Scheduler] : set Process {
	s.running + s.blocked + s.ready
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
  all p: Process | p in Scheduler.running => p.state = RUNNING and p in Scheduler.blocked => p.state = BLOCKED and p in Scheduler.ready => p.state = READY
  
  //no loop in process chain
  //no p: Process | p in (p.^nextProcess )
  //all p1, p2: Process | p1 != p2 => p1.nextProcess != p2 and p2.nextProcess != p1
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
	 s".blocked = s.blocked 
  }

}

pred runningToReady[s, s": Scheduler] {
   let runningProcess = s.running {
	one runningProcess
	runningProcess.state = READY

	s".running = none 
	//s".ready = s.ready + runningProcess 
	s".ready.nextProcess = runningProcess
	s".blocked = s.blocked 
   }
}

pred readyToBlocked[s,s": Scheduler] {
   let readyProcess = s.ready {
	one readyProcess
	readyProcess.state = BLOCKED

	s".ready = s.ready.nextProcess - readyProcess
	s".running = s.running 
	//s".blocked = s.blocked + readyProcess
	s".blocked = s.blocked + readyProcess
   }
}

pred blockedToReady[s,s":Scheduler] {
   let blockedProcess = s.blocked {
	one blockedProcess
	
	blockedProcess.state = READY

	s".ready = s.ready + blockedProcess
	//s".ready.nextProcess = blockedProcess
	s".blocked = s.blocked.nextProcess - blockedProcess 
	s".running = s.running
   }
}

pred runningToBlocked[s,s":Scheduler] {
   let runningProcess = s.running {
	one runningProcess
	runningProcess.state = BLOCKED

	s".ready = s.ready 
	//s".waiting = s.waiting + runningProcess and
	s".blocked.nextProcess = runningProcess
	s".running = none  
   }
}

fact {
	// init
	SO/first.ready = PO/first
	PO/first.state = READY
	SO/first.ready.nextProcess = PO/first.next
	SO/first.blocked = Process - (PO/first + PO/first.next)
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
