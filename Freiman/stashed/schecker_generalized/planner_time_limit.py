"""Interrupt discovery only; timeout leaves the obligation unproved."""
import signal


class PlannerTimeout(Exception):
    pass


def bounded_planner(search,seconds):
    if seconds<=0:raise ValueError('positive planner limit required')
    original=search.planner
    def wrapped(*args,**kwargs):
        previous=signal.getsignal(signal.SIGALRM)
        if signal.getitimer(signal.ITIMER_REAL)!=(0.0,0.0):
            raise RuntimeError('cannot replace an active process timer')
        def expire(signum,frame):raise PlannerTimeout()
        signal.signal(signal.SIGALRM,expire)
        signal.setitimer(signal.ITIMER_REAL,seconds)
        timed_out=False
        try:return original(*args,**kwargs)
        except PlannerTimeout:
            timed_out=True
            search.planner_timeouts=getattr(search,'planner_timeouts',0)+1
            return None
        finally:
            signal.setitimer(signal.ITIMER_REAL,0)
            signal.signal(signal.SIGALRM,previous)
            # Drop an unfinished native reply before the next request.
            if timed_out:search.close_native()
    return wrapped
