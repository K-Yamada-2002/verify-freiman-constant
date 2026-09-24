import signal
import time
from types import SimpleNamespace
import unittest
from planner_time_limit import bounded_planner

class PlannerTimerTests(unittest.TestCase):
    def test_timeout_is_no_proof_and_native_reply_is_discarded(self):
        events=[];old=signal.getsignal(signal.SIGALRM)
        search=SimpleNamespace(planner=lambda *a:time.sleep(1),close_native=lambda:events.append('closed'))
        self.assertIsNone(bounded_planner(search,.01)('pending'))
        self.assertEqual(search.planner_timeouts,1);self.assertEqual(events,['closed'])
        self.assertEqual(signal.getsignal(signal.SIGALRM),old)
        self.assertEqual(signal.getitimer(signal.ITIMER_REAL),(0.0,0.0))
    def test_success_and_real_error_are_preserved(self):
        search=SimpleNamespace(planner=lambda x:x,close_native=lambda:self.fail('unnecessary close'))
        self.assertEqual(bounded_planner(search,1)(('plan',['child'])),('plan',['child']))
        def fail():raise ValueError('real error')
        search.planner=fail
        with self.assertRaisesRegex(ValueError,'real error'):bounded_planner(search,1)()
        self.assertEqual(signal.getitimer(signal.ITIMER_REAL),(0.0,0.0))
if __name__=='__main__':unittest.main()
