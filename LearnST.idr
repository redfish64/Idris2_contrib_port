module LearnST

import Control.ST 

main : IO ()
main = putStrLn "hooel"

-- sillyProof : (x : Var) -> InState x (State Integer) [(x ::: State Integer)]
-- sillyProof x = Here

--     Can't find an implementation for InState x (State ()) [(x ::: State Integer)]
increment : (x : Var) -> STrans m () [x ::: State Integer]
                                     (const [x ::: State Integer])
increment x =                                      
 do
   num <- read x
   write x (num + 1)

   
         
-- increment x = 
--  doRead >>= doWrite x
--  where
--    doRead : STrans m Integer [x ::: State Integer]
--                                      (const [x ::: State Integer])
--    doRead = read x
   
--    doWrite : (x : Var) -> Integer -> (STrans m () [x ::: State Integer]
--                                      (const [x ::: State Integer]))
--    doWrite x num = write x (the Integer $ num + 1)
   
   -- num <- the (STrans _ Integer _ _) $ read x
   -- the (STrans _ () _ _) $ write x (num + 1)
 -- do
 --   num <- the (STrans _ Integer _ _) $ read x
 --   the (STrans _ () _ _) $ write x (num + 1)
   
  --            pure num
   -- the (STrans _ Integer _ _) $ read x
   -- read x
 -- do
 --   read x
 --   pure ()
                 --write x (num + 1)
  -- do num <- read x
  --            pure num

-- makeAndIncrement : Integer -> STrans m Integer [] (const [])
-- makeAndIncrement init = do var <- new init
--                            increment var
--                            x <- read var
--                            delete var
--                            pure x
