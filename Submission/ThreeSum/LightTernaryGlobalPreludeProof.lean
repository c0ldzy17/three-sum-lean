import Submission.ThreeSum.LightTernaryGlobalPrelude

noncomputable section
namespace ThreeSum.LightTernaryGlobalPreludeProof
open Light LightTernaryGlobalPrelude
open LightExtensionBackendLayout hiding params
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

def time (M b p K κ n free : ℕ) : ℕ :=
  let U:=n^κ
  let J:=LightTernaryDimensions.J M b n U
  let d:=LightTernaryDimensions.dim M b p K n U
  let q:=p^d
  LightNatPower.time κ+LightScales.time n+LightTernaryDimensions.time M b p K n U+
    LightExtensionBackendSetup.time (backend free) d p q J+LightNatPower.time 6+5000

private theorem dimensions_call {lim : Limits} {M b p K n U free depth : ℕ} [Fact p.Prime]
    (μ : ℕ→ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (hw : (lim.space:ℤ)≤lim.word) (hs : dimensions free+4≤lim.space)
    (hd : depth+1<lim.depth) (hword : (LightTernaryDimensions.word M b p K n U:ℤ)≤lim.word)
    (κ : ℕ) :
    Meets lim (program M b p K κ) 5 depth [n,U,dimensions free] μ
      (LightTernaryDimensions.time M b p K n U)
      (fun z ν=>z=((p^(LightTernaryDimensions.dim M b p K n U):ℕ):ℤ) ∧
        Seg ν (dimensions free) [(LightTernaryDimensions.r M n:ℤ),LightTernaryDimensions.J M b n U,
          LightTernaryDimensions.dim M b p K n U,(p^(LightTernaryDimensions.dim M b p K n U):ℕ)] ∧
        Kept μ ν (dimensions free)) :=by
  have hh:=ReportingHostRelocation.meets
    (LightTernaryDimensions.program_meets μ hM hb hn hw hs hd hword) LightScales.program
  have hh':=hh.append
    (LightExtensionBackendSetup.program.map (ReportingHostRelocation.relocate 9)++
      LightNatPower.program.map (ReportingHostRelocation.relocate 48)++[body M b p K κ])
  change Meets lim (dimensionsLibrary M b p K++
    (LightExtensionBackendSetup.program.map (ReportingHostRelocation.relocate 9)++
      LightNatPower.program.map (ReportingHostRelocation.relocate 48)++[body M b p K κ])) 5 depth _ _ _ _ at hh'
  convert hh' using 1
  unfold program libraries ReportingHostRelocation.program
  rw [backendLibrary_length]
  unfold backendLibrary ReportingHostRelocation.program
  rw [dimensionsLibrary_length]
  simp only [List.append_assoc]


private theorem backend_call {lim : Limits} {M b p K d q J free depth : ℕ} [Fact p.Prime]
    (μ : ℕ→ℤ) (hdim : 0<d) (hq : p^d=q)
    (hw : (lim.space:ℤ)≤lim.word) (hd : depth+14<lim.depth)
    (hs : backend free+reserve d p q J≤lim.space) (κ : ℕ) :
    Meets lim (program M b p K κ) 47 depth [p,d,q,J,backend free] μ
      (LightExtensionBackendSetup.time (backend free) d p q J)
      (fun z ν=>∃c<q, z=((c+1:ℕ):ℤ) ∧
        Irreducible (TernaryExtensionEncoding.monicOfCode (p:=p) d c) ∧
        (∀s<q*q, ∀i<J+2, ν (physical (backend free) d q J+s*(J+2)+i)=
          (LightExtensionSeedMatrix.value
            (TernaryExtensionEncoding.encodedMul
              (LightExtensionBackend.modulusMonic (factor (backend free) d p q J) c)) q p s
            (TernarySignedLayout.offset J i):ℤ)) ∧ Kept μ ν (backend free)) :=by
  have hh:=ReportingHostRelocation.meets
    (LightExtensionBackendSetup.program_meets μ hdim hq hw hd hs) (dimensionsLibrary M b p K)
  have hh':=hh.append (LightNatPower.program.map (ReportingHostRelocation.relocate 48)++[body M b p K κ])
  change Meets lim (backendLibrary M b p K++
    (LightNatPower.program.map (ReportingHostRelocation.relocate 48)++[body M b p K κ]))
    47 depth _ _ _ _ at hh'
  convert hh' using 1
  unfold program libraries ReportingHostRelocation.program
  rw [backendLibrary_length]
  simp only [List.append_assoc]


def Menu (ν : ℕ→ℤ) (base d p q J c : ℕ) [Fact p.Prime] : Prop :=
  ∀s<q*q, ∀i<J+2, ν (physical base d q J+s*(J+2)+i)=
    (LightExtensionSeedMatrix.value
      (TernaryExtensionEncoding.encodedMul
        (LightExtensionBackend.modulusMonic (factor base d p q J) c)) q p s
      (TernarySignedLayout.offset J i):ℤ)

/-- The entire once-per-input prelude is physically executed from [n,free].
Dimensions and the field menu are computed, never passed as input advice. -/
theorem meets {lim : Limits} {M b p K κ n free depth : ℕ} [Fact p.Prime]
    (μ : ℕ→ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (hw : (lim.space:ℤ)≤lim.word)
    (hspace : finish free (LightTernaryDimensions.dim M b p K n (n^κ)) p
      (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ))≤lim.space)
    (hdepth : depth+15<lim.depth)
    (hScales : ((1000*(n+1):ℕ):ℤ)≤lim.word)
    (hDimensions : (LightTernaryDimensions.word M b p K n (n^κ):ℤ)≤lim.word)
    (hU : ((n^κ:ℕ):ℤ)≤lim.word) (hκ : (κ:ℤ)≤lim.word) :
    Meets lim (program M b p K κ) 49 depth [n,free] μ (time M b p K κ n free)
      (fun z ν=>∃c<p^(LightTernaryDimensions.dim M b p K n (n^κ)),
        z=(free:ℤ) ∧
        Irreducible (TernaryExtensionEncoding.monicOfCode (p:=p)
          (LightTernaryDimensions.dim M b p K n (n^κ)) c) ∧
        Seg ν free (header n (n^κ) (LightTernaryDimensions.r M n)
          (LightTernaryDimensions.J M b n (n^κ)) (LightTernaryDimensions.dim M b p K n (n^κ)) p
          (p^(LightTernaryDimensions.dim M b p K n (n^κ))) free c) ∧
        Seg ν (params free) (LightScales.values n) ∧
        Menu ν (backend free) (LightTernaryDimensions.dim M b p K n (n^κ)) p
          (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ)) c ∧
        Kept μ ν free) :=by
  let U:=n^κ
  let R:=LightTernaryDimensions.r M n
  let J:=LightTernaryDimensions.J M b n U
  let D:=LightTernaryDimensions.dim M b p K n U
  let Q:=p^D
  let B:=D+p+Q+J+2
  have hDpos : 0<D :=TernaryExtensionEncoding.menuDegree_pos (p:=p) _ _
  have hBpos : 1≤B :=by dsimp [B]; omega
  have hres : reserve D p Q J≤lim.space :=by change backend free+reserve D p Q J≤lim.space at hspace; omega
  have hEnd : backend free+reserve D p Q J≤lim.space :=hspace
  have hB6 : B^6≤reserve D p Q J :=by change B^6≤100000000*B^6; omega
  have hB1 : B≤B^6 :=by simpa only [pow_one] using Nat.pow_le_pow_right hBpos (show 1≤6 by decide)
  have hBword : (B:ℤ)≤lim.word :=(Int.ofNat_le.mpr ((hB1.trans hB6).trans hres)).trans hw
  have hB6word : ((B^6:ℕ):ℤ)≤lim.word :=(Int.ofNat_le.mpr (hB6.trans hres)).trans hw
  have hcoeff : 100000000≤reserve D p Q J :=by
    have hh:=Nat.one_le_pow 6 B hBpos
    change 100000000≤100000000*B^6
    nlinarith
  have hcoeffWord : (100000000:ℤ)≤lim.word :=(Int.ofNat_le.mpr (hcoeff.trans hres)).trans hw
  have hBase : backend free≤lim.space :=by omega
  have hfreeEnd : free+33≤lim.space :=by simpa only [backend] using hBase
  have hpWord : (p:ℤ)≤lim.word :=by dsimp [B] at hBword; omega
  have h6 : (6:ℤ)≤lim.word :=by omega
  have hPower (i : ℕ) (hi : i≤κ) : ((n^i:ℕ):ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hn hi)).trans hU
  have hFinalPower (i : ℕ) (hi : i≤6) : ((B^i:ℕ):ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hBpos hi)).trans hB6word
  have hpowers : (program M b p K κ)[48]?=some LightNatPower.body :=by
    unfold program
    rw [List.getElem?_append_left (by simp)]
    unfold libraries ReportingHostRelocation.program
    rw [List.getElem?_append_right (by simp)]
    simp [backendLibrary_length,LightNatPower.program,LightNatPower.body]
  have hSc : LightScales.Procs (program M b p K κ) 0 :=by constructor <;> rfl
  have hscSpace : params free+5≤lim.space :=by unfold params; omega
  have hdimSpace : dimensions free+4≤lim.space :=by unfold dimensions; omega
  have hPow:=LightNatPower.meets (d:=depth+1) hpowers μ hκ hPower
  have hPhysicalEnd : physical (backend free) D Q J≤lim.space :=by
    have hh:=LightExtensionBackendLayout.end_le (backend free) D p Q J
    have hb : physical (backend free) D Q J≤sum (backend free) D Q J+2*D :=by
      unfold sum prod LightExtensionBackendLayout.r h LightExtensionBackendLayout.b a; omega
    exact hb.trans (hh.trans hEnd)
  have hPhysicalCalc : (backend free:ℤ)+4*(D:ℤ)+11+(Q:ℤ)*(Q:ℤ)+
      (Q:ℤ)*(Q:ℤ)*((J:ℤ)+2)≤lim.word :=by
    have hh : (physical (backend free) D Q J:ℤ)≤lim.word :=(Int.ofNat_le.mpr hPhysicalEnd).trans hw
    simp only [physical,logical,table,ctx,target,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] at hh
    convert hh using 1 <;> ring
  have hQQ : ((Q*Q:ℕ):ℤ)≤lim.word :=by
    have hh : Q*Q≤physical (backend free) D Q J :=by unfold physical logical; omega
    exact (Int.ofNat_le.mpr (hh.trans hPhysicalEnd)).trans hw
  have hlen : ((J+2:ℕ):ℤ)≤lim.word :=by dsimp [B] at hBword; omega
  have hpartial : (backend free:ℤ)+4*(D:ℤ)+11+(Q:ℤ)*(Q:ℤ)≤lim.word :=by
    have hz : 0≤(Q:ℤ)*(Q:ℤ)*((J:ℤ)+2) :=by positivity
    omega
  have hproduct : (Q:ℤ)*(Q:ℤ)*((J:ℤ)+2)≤lim.word :=by omega
  have hQ0 : (0:ℤ)≤(p:ℤ)^D :=by positivity
  have hQQ0 : (0:ℤ)≤(Q:ℤ)*(Q:ℤ) :=by positivity
  have hprod0 : (0:ℤ)≤(Q:ℤ)*(Q:ℤ)*((J:ℤ)+2) :=by positivity
  have hreserveCalc : (backend free:ℤ)+100000000*(B:ℤ)^6≤lim.word :=by
    have hh : (backend free+reserve D p Q J:ℤ)≤lim.word :=(Int.ofNat_le.mpr hEnd).trans hw
    change (backend free+100000000*B^6:ℤ)≤lim.word at hh
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hh
  have hReserveProd : (100000000:ℤ)*(B:ℤ)^6≤lim.word :=by omega
  have hReserve0 : (0:ℤ)≤100000000*(B:ℤ)^6 :=by positivity
  simp only [U,R,J,D,Q,B,backend,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]
    at hQ0 hQQ hQQ0 hlen hPhysicalCalc hpartial hproduct hprod0 hBword hReserveProd hReserve0 hreserveCalc
  apply Meets.of_body (show (program M b p K κ)[49]?=some (body M b p K κ) from by
    unfold program
    rw [List.getElem?_append_right (by simp)]
    simp only [libraries_length,Nat.sub_self,List.getElem?_cons_zero])
  unfold body time
  light_call hPow using U with magnitude μp ⟨hMagnitude,hμp⟩
  subst μp
  light_set (params free:ℕ) using params
  light_set (dimensions free:ℕ) using params,dimensions
  light_set (backend free:ℕ) using U,R,J,D,Q,params,dimensions,backend
  light_call (hSc.meets (d:=depth+1) (μ:=μ) hw hscSpace hScales (by omega)) using U,R,J,D,Q,params,dimensions,backend
    with scales μs ⟨hScalesResult,hScalesSeg,hScalesKeep⟩
  have hDim':=dimensions_call (depth:=depth+1) μs hM hb hn hw hdimSpace (by omega) hDimensions κ
  light_call hDim' using U,R,J,D,Q,params,dimensions,backend,U,hMagnitude with dims μd ⟨hDimResult,hDimSeg,hDimKeep⟩
  have hread (i : ℕ) (hi : i<4) :=hDimSeg i (by simpa using hi)
  have ha0 : ((dimensions free:ℤ)).toNat=dimensions free :=by omega
  have ha1 : ((dimensions free:ℤ)+1).toNat=dimensions free+1 :=by omega
  have ha2 : ((dimensions free:ℤ)+2).toNat=dimensions free+2 :=by omega
  have ha3 : ((dimensions free:ℤ)+3).toNat=dimensions free+3 :=by omega
  have hr : μd (dimensions free)=(R:ℤ) :=by simpa [R] using hread 0 (by decide)
  have hj : μd (dimensions free+1)=(J:ℤ) :=by simpa [J,U] using hread 1 (by decide)
  have hd : μd (dimensions free+2)=(D:ℤ) :=by simpa [D,U] using hread 2 (by decide)
  have hq : μd (dimensions free+3)=(Q:ℤ) :=by simpa [Q,D,U] using hread 3 (by decide)
  have hf29 : ((free:ℤ)+29).toNat=free+29 :=by omega
  have hf30 : ((free:ℤ)+30).toNat=free+30 :=by omega
  have hf31 : ((free:ℤ)+31).toNat=free+31 :=by omega
  have hf32 : ((free:ℤ)+32).toNat=free+32 :=by omega
  have hf291 : ((free:ℤ)+29+1).toNat=free+30 :=by omega
  have hf292 : ((free:ℤ)+29+2).toNat=free+31 :=by omega
  have hf293 : ((free:ℤ)+29+3).toNat=free+32 :=by omega
  simp only [dimensions,Nat.add_assoc,Nat.reduceAdd] at hr hj hd hq
  have hRWord : (R:ℤ)≤lim.word :=by dsimp [R]; unfold LightTernaryDimensions.word at hDimensions; omega
  have hJWord : (J:ℤ)≤lim.word :=by dsimp only [J,U]; omega
  have hDWord : (D:ℤ)≤lim.word :=by dsimp only [D,U]; omega
  have hQWord : (Q:ℤ)≤lim.word :=by dsimp only [Q,D,U]; push_cast; omega
  light_set R using U,R,J,D,Q,params,dimensions,backend,hr,ha0,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_set J using U,R,J,D,Q,params,dimensions,backend,hj,ha1,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_set D using U,R,J,D,Q,params,dimensions,backend,hd,ha2,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_set Q using U,R,J,D,Q,params,dimensions,backend,hq,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_call (backend_call (depth:=depth+1) μd hDpos rfl hw (by omega) hEnd κ)
    using U,R,J,D,Q,params,dimensions,backend,hr,hj,hd,hq,ha0,ha1,ha2,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
    with irreducible μb ⟨c,hc,hIrredResult,hIrred,hMenu,hBackendKeep⟩
  light_set (Q*Q:ℕ) using U,R,J,D,Q,params,dimensions,backend,hr,hj,hd,hq,ha0,ha1,ha2,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_set (J+2:ℕ) using U,R,J,D,Q,params,dimensions,backend,hr,hj,hd,hq,ha0,ha1,ha2,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_set (physical (backend free) D Q J:ℕ)
    using U,R,J,D,Q,params,dimensions,backend,physical,logical,table,ctx,target,hr,hj,hd,hq,ha0,ha1,ha2,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_set B using U,R,J,D,Q,B,params,dimensions,backend,hr,hj,hd,hq,ha0,ha1,ha2,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_call (LightNatPower.meets (d:=depth+1) hpowers μb h6 hFinalPower)
    using U,R,J,D,Q,B,params,dimensions,backend with finalPower μb' ⟨hFinalPowerResult,hμb'⟩
  subst μb'
  simp only [U,J,D,Q,B,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hFinalPowerResult
  light_set (finish free D p Q J:ℕ)
    using U,R,J,D,Q,finish,reserve,LightExtensionBackendLayout.params,B,params,dimensions,backend,hFinalPowerResult,
      hr,hj,hd,hq,ha0,ha1,ha2,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_store free n using U,R,J,D,Q,params,dimensions,backend
  light_store (free+1) U using U,R,J,D,Q,params,dimensions,backend,U,hMagnitude
  light_store (free+2) R using U,R,J,D,Q,params,dimensions,backend,hr,ha0,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_store (free+3) J using U,R,J,D,Q,params,dimensions,backend,hj,ha1,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_store (free+4) D using U,R,J,D,Q,params,dimensions,backend,hd,ha2,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_store (free+5) Q using U,R,J,D,Q,params,dimensions,backend,hq,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_store (free+6) (params free) using U,R,J,D,Q,params,dimensions,backend
  light_store (free+7) (physical (backend free) D Q J) using U,R,J,D,Q,params,dimensions,backend,
    physical,logical,table,ctx,target,hr,hj,hd,hq,ha0,ha1,ha2,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_store (free+8) (finish free D p Q J) using U,R,J,D,Q,params,dimensions,backend,finish,reserve,
    LightExtensionBackendLayout.params,B,hFinalPowerResult,hr,hj,hd,hq,ha0,ha1,ha2,ha3,hf29,hf30,hf31,hf32,hf291,hf292,hf293
  light_store (free+9) (c+1:ℕ) using U,R,J,D,Q,params,dimensions,backend,hIrredResult
  light_set free using U,R,J,D,Q,params,dimensions,backend
  refine ⟨c,hc,rfl,hIrred,?_,?_,?_,?_⟩
  · intro i hi
    have hi10 : i<10 :=by simpa [header] using hi
    interval_cases i <;> simp [header,U,R,J,D,Q,params,finish]
  · intro i hi
    have hi5 : i<5 :=by simpa [LightScales.values] using hi
    simp only [params] at *
    simp only [Function.update_of_ne (by omega : free+10+i≠free+9),
      Function.update_of_ne (by omega : free+10+i≠free+8),Function.update_of_ne (by omega : free+10+i≠free+7),
      Function.update_of_ne (by omega : free+10+i≠free+6),Function.update_of_ne (by omega : free+10+i≠free+5),
      Function.update_of_ne (by omega : free+10+i≠free+4),Function.update_of_ne (by omega : free+10+i≠free+3),
      Function.update_of_ne (by omega : free+10+i≠free+2),Function.update_of_ne (by omega : free+10+i≠free+1),
      Function.update_of_ne (by omega : free+10+i≠free)]
    rw [hBackendKeep _ (by unfold backend; omega),hDimKeep _ (by unfold dimensions; omega)]
    exact hScalesSeg i hi
  · change Menu _ (backend free) D p Q J c
    intro seed hseed i hi
    have hsep : free+10≤physical (backend free) D Q J :=by
      unfold physical logical table ctx target backend
      omega
    simp only [Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+9),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+8),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+7),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+6),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+5),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+4),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+3),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+2),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free+1),
      Function.update_of_ne (by omega : physical (backend free) D Q J+seed*(J+2)+i≠free)]
    exact hMenu seed hseed i hi
  · intro x hx
    simp only [Function.update_of_ne (by omega : x≠free+9),Function.update_of_ne (by omega : x≠free+8),
      Function.update_of_ne (by omega : x≠free+7),Function.update_of_ne (by omega : x≠free+6),
      Function.update_of_ne (by omega : x≠free+5),Function.update_of_ne (by omega : x≠free+4),
      Function.update_of_ne (by omega : x≠free+3),Function.update_of_ne (by omega : x≠free+2),
      Function.update_of_ne (by omega : x≠free+1),Function.update_of_ne (by omega : x≠free)]
    rw [hBackendKeep x (by unfold backend; omega),hDimKeep x (by unfold dimensions; omega),
      hScalesKeep x (Or.inl (by unfold params; omega))]

end ThreeSum.LightTernaryGlobalPreludeProof
