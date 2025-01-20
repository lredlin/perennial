package heap


import (
   "fmt"
   "sync"
   "time"
)


type UnbufferedChannel struct {
   mu             *sync.Mutex
   v              uint64
   receiver_ready bool
   sender_ready   bool
   receiver_done  bool
   sender_done    bool
   closed         bool
}


func NewUnbufferedChannel() *UnbufferedChannel {
   return &UnbufferedChannel{mu: new(sync.Mutex)}
}


func (c *UnbufferedChannel) Send(val uint64) {
   var return_early = false
   for {
       c.mu.Lock()
       if c.receiver_ready {
           c.receiver_ready = false
           c.sender_done = true
           c.v = val
           c.mu.Unlock()
           return_early = true
           break
       }
       if c.closed {
           panic("send on closed channel")
       }
       if !c.receiver_ready && !c.sender_ready && !c.receiver_done && !c.sender_done {
           c.sender_ready = true
           c.v = val
           c.mu.Unlock()
           break
       }
       c.mu.Unlock()
   }
   if return_early {
       for {
           c.mu.Lock()
           if !c.sender_done {
               c.mu.Unlock()
               break
           }
           c.mu.Unlock()
       }
       return
   }
   for {
       c.mu.Lock()
       if c.receiver_done {
           c.receiver_done = false
           c.mu.Unlock()
           break
       }
       if c.closed {
           panic("send on closed channel")
       }
       c.mu.Unlock()


   }
}


func (c *UnbufferedChannel) Receive() (uint64, bool) {
   var return_early = false
   var closed = false
   var ret_val = uint64(0)
   for {
       c.mu.Lock()
       if c.closed {
           c.mu.Unlock()
           closed = true
           break
       }
       if c.sender_ready {
           c.sender_ready = false
           c.receiver_done = true
           ret_val = c.v
           c.mu.Unlock()
           return_early = true
           break
       }
       if !c.receiver_ready && !c.sender_ready && !c.receiver_done && !c.sender_done {
           c.receiver_ready = true
           c.mu.Unlock()
           break
       }
       c.mu.Unlock()
   }
   if closed {
       return 0, true
   }
   if return_early {
       for {
           c.mu.Lock()
           if !c.receiver_done {
               c.mu.Unlock()
               break
           }
           c.mu.Unlock()
       }
       return ret_val, false
   }
   for {
       c.mu.Lock()
       if c.closed {
           c.mu.Unlock()
           closed = true
           break
       }
       if c.sender_done {
           c.sender_done = false
           ret_val = c.v
           c.mu.Unlock()
           break
       }
       c.mu.Unlock()
   }
   return ret_val, closed


}


func (c *UnbufferedChannel) Close() {
   c.mu.Lock()
   if c.closed {
       panic("send on closed channel")
   }
   c.receiver_ready = false
   c.sender_ready = false
   c.closed = true
   c.mu.Unlock()
}


func (c *UnbufferedChannel) TryReceive() (uint64, bool) {
   var ret_val = uint64(0)
   var return_bool = false
   c.mu.Lock()
   if c.closed {
       ret_val = 0
   } else {
       if c.sender_ready {
           c.sender_ready = false
           c.receiver_done = true
           ret_val = c.v
           return_bool = true
       }
   }
   c.mu.Unlock()
   if return_bool {
       for {
           c.mu.Lock()
           if !c.receiver_done{
               break
           }
           c.mu.Unlock()
       }
   }
   return ret_val, return_bool
}


func (c *UnbufferedChannel) TrySend(val uint64) bool {
   var return_bool = false
   c.mu.Lock()
   if c.closed {
       panic("Send on closed channel.")
   }
   if c.receiver_ready {
       c.receiver_ready = false
       c.sender_done = true
       c.v = val
       return_bool = true
   }
   c.mu.Unlock()
   if return_bool {
       for {
           c.mu.Lock()
           if !c.sender_done {
               break
           }
           c.mu.Unlock()
       }
   }
   return return_bool
}


func Source(src []uint64) *UnbufferedChannel {
   c := NewUnbufferedChannel()
   go func() {
       for _, v := range src {
           c.Send(v)
       }
       c.Close()
   }()
   return c
}


func Map(mapper func(uint64) uint64, input *UnbufferedChannel) *UnbufferedChannel {
   c := NewUnbufferedChannel()
   go func() {
       curr_val := uint64(0)
       closed := false
       for {
           curr_val, closed = input.Receive()
           fmt.Println(curr_val)
           if closed {
               c.Close()
               break
           }
           c.Send(curr_val)
       }
   }()
   return c
}


func Filter(filter func(uint64) bool, input *UnbufferedChannel) *UnbufferedChannel {
   c := NewUnbufferedChannel()
   go func() {
       curr_val := uint64(0)
       closed := false
       for {
           curr_val, closed = input.Receive()
           if closed {
               c.Close()
               break
           }
           if filter(curr_val) {
               c.Send(curr_val)
           }
       }
   }()
   return c
}


func Reduce(reducer func(uint64, uint64) uint64, input *UnbufferedChannel) *UnbufferedChannel {
   c := NewUnbufferedChannel()
   curr_val := uint64(0)
   total := uint64(0)
   go func() {
       closed := false
       for {
           curr_val, closed = input.Receive()
           if closed {
               c.Send(total)
               c.Close()
               break
           }
           total = reducer(total, curr_val)
       }
   }()
   return c
}


func Sink(input *UnbufferedChannel) []uint64 {
   s := make([]uint64, 1)
   curr_val := uint64(0)
   closed := false
   for {
       curr_val, closed = input.Receive()
       if closed {
           break
       }
       s = append(s, curr_val)
   }
   return s
}
