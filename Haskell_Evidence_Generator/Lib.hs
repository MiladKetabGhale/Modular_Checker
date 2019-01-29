{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

module Lib where

import Data.Ratio
import Data.List



{--candidates--}
data Cand =
  WHC
 |BAB
 |PAF
 |SEZ
 |THP
 |LOL
 |BUJ
 |KEG
 |HAJ
 |FAT
 |TAK
 |TAG 
 |CRH
 |ONB
 |ALJ
 |MUR
 |ROS
 |CUD
 |GES
 |EVK
 |LAA
 |SEA
 |VON
 |HOA
 |SAO
 |SCN
 |MCD
 |PID
 |RAS
 |LEC
 |KIE
 |HEM
 |COS
 |BAA
 |CRL
 |GAK
 |MAD
 |BAE
 |JOG
 |OND deriving (Show, Eq, Ord, Read) 



{--  RAS
 |KEA
 |LEC
 |SIA
 |JHT
 |GAK
 |BAA
 |COS
 |DRA
 |GAI
 |FIM
 |MAD
 |KUM
 |DIS
 |BOT
 |BIS
 |HAJ
 |DOS
 |LEE
 |JOG
 |MIJ
 |SET
 |GOM
 |CUM
 |CUD
 |POP deriving (Show,Eq,Ord,Read)
--}

{--
  PAH
 |GIN
 |HEC
 |HIJ
 |COA
 |CHD
 |HAT
 |BUC
 |EZE
 |HUM
 |TAG
 |WAD
 |LEM
 |JBN
 |JAM
 |BEY
 |BOC
 |NAM
 |LEK
 |MCG
 |VAJ
 |POM
 |REK
 |THM
 |HNJ
 |BIM
 |WAM
 |DUV deriving (Show, Eq, Read, Ord)
 --}

{-- cands of Brindabella 2012
  GEM
 |DAJ
 |SEZ
 |WAA
 |MAK
 |GIM
 |JEV
 |COR
 |BUJ
 |KIM
 |MUB
 |BRA
 |ERM
 |DOB
 |JOK
 |PEC
 |LIM
 |HEA
 |LAN
 |SMB
 --}

{--
  RAS
 |KEA
 |LEC
 |SIA
 |JHT
 |GAK
 |BAA
 |COS
 |DRA
 |GAI
 |FIM
 |MAD
 |KUM
 |DIS
 |BOT
 |BIS
 |HAJ
 |DOS
 |LEE
 |JOG
 |MIJ
 |SET
 |GOM
 |CUM
 |CUD
 |POP deriving (Show,Eq,Ord,Read)
--}

{--list of all candidates--}
cand_all :: [Cand]
cand_all = [WHC,BAB,PAF,SEZ,THP,LOL,BUJ,KEG,HAJ,FAT,TAK,TAG,CRH,ONB,ALJ,MUR,ROS,CUD,GES,EVK,LAA,SEA,VON,HOA,SAO,SCN,MCD,PID,RAS,LEC,KIE,HEM,COS,BAA,CRL,GAK,MAD,BAE,JOG,OND] 



--[RAS,KEA,LEC,SIA,JHT,GAK,BAA,COS,DRA,GAI,FIM,MAD,KUM,DIS,BOT,BIS,HAJ,DOS,LEE,JOG,MIJ,SET,GOM,CUM,CUD,POP]
 


--[PAH,GIN,HEC,HIJ,COA,CHD,HAT,BUC,EZE,HUM,TAG,WAD,LEM,JBN,JAM,BEY,BOC,NAM,LEK,MCG,VAJ,POM,REK,THM,HNJ,BIM,WAM,DUV]

--cand_all = [GEM,DAJ,SEZ,WAA,MAK,GIM,JEV,COR,BUJ,KIM,MUB,BRA,ERM,DOB,JOK,PEC,LIM,HEA,LAN,SMB]
  

--[RAS,KEA,LEC,SIA,JHT,GAK,BAA,COS,DRA,GAI,FIM,MAD,KUM,DIS,BOT,BIS,HAJ,DOS,LEE,JOG,MIJ,SET,GOM,CUM,CUD,POP]



 




{--
data Cand = 
 |A
 |C
 |D deriving (Show,Eq,Read,Ord)
 

cand_all = [A,B,C,D]
--}

type Parameters = (Ratio Integer, Int, [Cand])

type Ballot = [([Cand], Ratio Integer)] 

type Tally = Cand -> Ratio Integer

type Pile = Cand -> [Ballot] 

data Judgement =  NonFinal 
                          Ballot 
                          Tally 
                          Pile 
                          [Cand]
                          [Cand] 
                          [Cand] 
                          [Cand]
                | Final [Cand] 

 
instance Show (Judgement) where
 show (NonFinal a b c d e f g) = (show a) ++ "; " ++
                               (show b) ++ "; " ++
                               (show c) ++ "; " ++
                               (show d) ++ "; " ++
                               (show e) ++ "; " ++
                               (show f) ++ ";" ++
                               (show g)
 show (Final l) = show l

instance (Show a) => Show (Cand -> a) where
  show f = show_l cand_all where
    show_l [] = ""
    show_l [c] = (show c) ++ "{" ++ (show (f c)) ++ "}"
    show_l (c:cs) = (show c) ++ "{" ++ (show (f c)) ++ "} " ++ (show_l cs)

isWeakestCand :: Tally -> [Cand] -> Maybe Cand 
isWeakestCand t h = case h of
                         [] -> Nothing
                         h0:hs -> if (t h0 <= (minimum $ map t h)) then Just h0 else isWeakestCand t hs  


removeJust :: Maybe Cand -> Cand
removeJust Nothing = error "nothing to return"
removeJust (Just c) = c


                                                                              
tally :: Tally
tally = \c -> 0 % 1

pile :: Pile
pile = \c -> [] 


repeatFunction 0 f a = a
repeatFunction n f a = f $ repeatFunction (n -1) f a

ordOnce :: Tally -> [Cand] -> [Cand]
ordOnce t [] = []
ordOnce t [x] = [x]
ordOnce t (x:y:ys) = if (t x) <= (t y) then x: (ordOnce t (y:ys)) else y:(ordOnce t (x:ys))

{--
updatePiles :: Ratio Integer -> Pile -> Tally -> [Cand] -> Pile
updatePiles qu p t l1 = \d -> if elem d l1 then 
                                    map (\b -> 
                                              (fst b, (snd b) * 
                                              (update))) (p d)
                              else p d  
--}

transVal :: Tally -> Cand -> Ratio Integer -> Ratio Integer -> Ratio Integer
transVal t c qu r = ((t c) - qu) * (denominator r % 1) * (1 % numerator r)


sumRats :: Ratio Integer -> Ratio Integer -> Ratio Integer
sumRats x y = x + y  

sumListRatsAux :: Ballot -> Ratio Integer -> Ratio Integer
sumListRatsAux [] acc = acc
sumListRatsAux (b0 : bs) acc = sumListRatsAux bs (acc + (snd b0))

sumListRats l = sumListRatsAux l (0 % 1)

sumParcel :: Cand -> Pile -> Ratio Integer
sumParcel c p = sumListRats (last (p c))

actTransferVal :: Pile -> Tally -> Ratio Integer -> Cand -> Ratio Integer
actTransferVal  p t qu c = let sp = sumParcel c p in
                            let tv = transVal t c qu sp in
                              if (sp /= 0 % 1) && (tv <= 1 % 1) then tv else 1 % 1                             

{--
if ((sumParcel c p) /= 0 % 1) && (transVal t c qu (sumParcel c p) <= 1 % 1) then (transVal t c qu (sumParcel c p)) else (1 % 1)
--}                                

updatePilesACT :: Ratio Integer -> Pile -> Tally -> [Cand] -> Pile
updatePilesACT qu p t l1 = \d -> if elem d l1 then
                                  let tv = actTransferVal p t qu d in
                                   let lastParcel = map (\b ->
                                                     (fst b, ((snd b) * tv))) $ last (p d) in [lastParcel]
                                 else p d


firstContinuingCand :: Cand -> [Cand] -> [Cand] -> Bool
firstContinuingCand c h [] = False
firstContinuingCand c h (b0:bs) = if (c == b0) then True
                                   else (notElem b0 h) && firstContinuingCand c h bs  


elimRule :: Parameters -> Judgement -> Judgement
elimRule (qu,st,l) (NonFinal [] t p [] [] e h) =
          --    if (length $ e ++ h) > st &&
                if (all ( < qu) $ map t h)
                   then let c = removeJust $ isWeakestCand t h
                        in NonFinal
                            (concat (p c)) t
                            (\d -> if d /= c then p d else []) [] [] e
                            (delete c h)
                 else (error "invalid elimRule app")
elimRule (qu,st,l) _ = error "invalid state reached"

electRule :: Parameters -> Judgement -> Judgement
electRule (qu,st,l) (NonFinal [] t p bl [] e h) =
              let l1 = filter (\c -> qu <= (t c)) h
              in
                let l2 = reverse $ (repeatFunction (length l1 - 1) (ordOnce t) l1)
                in
                  let l3 = take (st - (length e)) l2
                  in NonFinal
                       [] t
                       (updatePilesACT qu p t l3)
                       (bl ++ l3)
                       []
                       (e ++ l3)
                       (h \\ l3)
electRule (qu,st,l) _ = error "invalid electRule app"


countRule :: Parameters -> Judgement -> Judgement
countRule (qu,st,l) (NonFinal ba t p bl bl2 e h) =
    if not (null ba) then
      let  f = (\c -> if elem c h then 
                         let l' = filter (\b -> firstContinuingCand c h (fst b)) ba
                         in  ((t c) + (sum $ map snd l'), (p c) ++ [l']) 
                      else (t c, p c))
      in NonFinal [] (fst . f) (snd . f) bl [] e h
    else (error "invalid countRule app")                                                       
countRule (qu,st,l) _ = error "invalid countRule app"


transferRule :: Parameters -> Judgement -> Judgement
transferRule (qu,st,l) (NonFinal [] t p (bl0:bls) [] e h) =
   if all ( < qu) (map t h) then NonFinal (concat (p bl0)) t 
                                          (\c -> if (c /= bl0) then (p c) else [])
                                          bls [] e h
   else (error "invalid transferRule app")
transferRule (qu,st,l) _ = error "invalid transferRule app"


hwinRule :: Parameters -> Judgement -> Judgement
hwinRule (qu,st,l) (NonFinal ba t p bl bl2 e h) = Final $ e ++ h
hwinRule (qu,st,l) _ = error "invalid hwinRule app"

ewinRule :: Parameters -> Judgement -> Judgement
ewinRule (qu,st,l) (NonFinal ba t p bl bl2 e h) = Final e
ewinRule (qu,st,l) _ = error "invalid ewinRule app"

 
voteCounting :: Parameters -> Judgement -> Judgement
voteCounting (qu,st,l) (NonFinal ba t p bl bl2 e h) = 
  if (length $ e ++ h) <= st then hwinRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
   else if (length e == st) then ewinRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
         else if not (null ba) then voteCounting (qu,st,l) $ 
                                      countRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
               else if any (qu <= ) (map t h) then voteCounting (qu,st,l) $
                                                    electRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
                     else if null bl then voteCounting (qu,st,l) $
                                            elimRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
                            else voteCounting (qu,st,l) $ 
                                   transferRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
voteCounting (qu,st,l) _ = error "invalid state reached"



countingTrace (qu,st,l) acc (NonFinal ba t p bl bl2 e h) =  
   if (length $ e ++ h) <= st then (hwinRule (qu,st,l) (NonFinal ba t p bl bl2 e h)):(NonFinal ba t p bl bl2 e h):acc
    else if (length e == st) then (ewinRule (qu,st,l) (NonFinal ba t p bl bl2 e h)):(NonFinal ba t p bl bl2 e h):acc
           else if not (null ba) then countingTrace (qu,st,l) ((NonFinal ba t p bl bl2 e h):acc) $
                                      countRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
               else if any (qu <= ) (map t h) then countingTrace (qu,st,l) ((NonFinal ba t p bl bl2 e h):acc) $
                                                    electRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
                     else if null bl then countingTrace (qu,st,l) ((NonFinal ba t p bl bl2 e h):acc) $
                                            elimRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
                                     else  countingTrace (qu,st,l) ((NonFinal ba t p bl bl2 e h):acc) $
                                               transferRule (qu,st,l) (NonFinal ba t p bl bl2 e h)
                                 

--printTrace (qu,st,l) ba = mapM_ print (countingTrace (qu,st,l) [] (NonFinal ba tally pile [] [] cand_all)) 
 
