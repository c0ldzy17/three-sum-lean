import Submission.ThreeSum.LightBandLookup

/-!
# Actual rectangular tables of band-owner lookups

Each output cell is a real call to the division-free interval lookup.
The two fixed outer counters identify the owner coordinates; the cell stores
zero for a miss or the third coordinate plus one. Keeping harmless candidate
duplicates is sufficient for the quadratic work bound and avoids any cubic
triple filtering operation.
-/

namespace ThreeSum.LightBandTable

open Light ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def rowValue (lo hi : ℕ → ℤ) (n : ℕ) (x s : ℤ) (f : ℕ → ℤ) (j : ℕ) : ℕ :=
  LightBandLookup.result lo hi n (s*x+f j)

/-- Arguments: left value, right base, target endpoints, right length,
target length, output, powers, width, left sign. -/
def rowBody (pLookup : ℕ) : Stmt :=
  .for 10 (v 4) (
    .call pLookup [v 2,v 3,v 5,v 9 *' v 0 +' M (v 1 +' v 10),v 7,v 8] 11 ;;
    .store (v 6 +' v 10) (v 11))

def rowTime (n W : ℕ) : ℕ := n*(LightBandLookup.time W+60)+6

theorem row_meets {pRow pLookup pSearch b loBase hiBase n m dst powers W d U : ℕ}
    {x s : ℤ} (hrow : P[pRow]? = some (rowBody pLookup))
    (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hb : b+n ≤ dst) (hlo : loBase+m ≤ dst) (hhi : hiBase+m ≤ dst)
    (hdst : dst+n ≤ powers) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hqueryWord : 2*(U : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (b+j) = f j)
    (hreadLo : ∀ j < m, μ (loBase+j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase+j) = hi j)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j)
    (hm : m < 2^W) (hs : |s| ≤ 1) (hx : |x| ≤ U)
    (hf : ∀ j < n, |f j| ≤ U) (hd : d+W+2 ≤ lim.depth) :
    Meets lim P pRow d [x,b,loBase,hiBase,n,m,dst,powers,W,s] μ (rowTime n W)
      (fun _ μ' =>
        (∀ j < n, μ' (dst+j) = (rowValue lo hi m x s f j : ℤ)) ∧
        SameOutside μ μ' dst n) := by
  let F := fun j => (rowValue lo hi m x s f j : ℤ)
  have hsx : |s*x| ≤ (U : ℤ) := by
    rw [abs_mul]
    exact (mul_le_mul hs hx (abs_nonneg _) (by omega)).trans (by simp)
  have hsxBounds := abs_le.mp hsx
  have hquery (j : ℕ) (hj : j < n) : |s*x+f j| ≤ 2*(U : ℤ) := by
    exact (abs_add_le _ _).trans (by have := hf j hj; omega)
  apply Meets.of_body hrow
  unfold rowBody rowTime
  refine Ends.for
    (fun j σ => ∃ r : ℤ,
      σ = ⟨frame [x,b,loBase,hiBase,n,m,dst,powers,W,s,j,r],wrote μ dst F j⟩)
    n (LightBandLookup.time W+52) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,?_⟩
    simp [update_frame_setLocal,wrote_zero]
    simpa using (frame_append_zeros [x,b,loBase,hiBase,n,m,dst,powers,W,s,0] 1).symm
  case round =>
    rintro j _ hj _ ⟨r,rfl⟩
    have hread' : ∀ k < n, wrote μ dst F j (b+k) = f k := by
      intro k hk
      rw [wrote_rest (by omega)]
      exact hread k hk
    have hlo' : ∀ k < m, wrote μ dst F j (loBase+k) = lo k := by
      intro k hk
      rw [wrote_rest (by omega)]
      exact hreadLo k hk
    have hhi' : ∀ k < m, wrote μ dst F j (hiBase+k) = hi k := by
      intro k hk
      rw [wrote_rest (by omega)]
      exact hreadHi k hk
    have hpowers' : Powers (wrote μ dst F j) powers W := by
      intro k hk
      rw [wrote_rest (by omega)]
      exact hpowers k hk
    have hr := hread' j hj
    have hfBounds := abs_le.mp (hf j hj)
    have hqueryBounds := abs_le.mp (hquery j hj)
    light_call (LightBandLookup.meets (d := d+1) (L := W) (x := s*x+f j) hlookup hsearch
      (wrote μ dst F j) lo hi hw (by omega) (by omega) hspace hword hlo' hhi'
      hpowers' hsorted le_rfl hm (by omega))
      using hr,LightBandLookup.time,LightBandLookup.searchTime
      with result μ' ⟨hresult,hmem⟩
    subst μ'
    light_store (dst+j) (F j) using F,rowValue,hresult,
      LightBandLookup.time,LightBandLookup.searchTime
    refine ⟨by simp,result,?_⟩
    simp [update_frame_setLocal,wrote_succ]
  case done =>
    rintro _ _ ⟨r,rfl⟩
    exact ⟨fun j hj => wrote_done (μ := μ) (dst := dst) (f := F) hj,by light_keep⟩
  case bound =>
    rintro j _ _ _ ⟨r,rfl⟩
    simp

/-- Arguments: the two query-endpoint bases, target endpoint bases, both
owner dimensions, target size, output, powers, width, left sign. -/
def body (pRow : ℕ) : Stmt :=
  .for 11 (v 4) (
    .call pRow [M (v 0 +' v 11),v 1,v 2,v 3,v 5,v 6,
      v 7 +' v 11 *' v 5,v 8,v 9,v 10] 12)

def time (nX nY W : ℕ) : ℕ := nX*(rowTime nY W+70)+6

theorem meets {pMain pRow pLookup pSearch a b loBase hiBase nX nY m dst powers W d U : ℕ}
    {s : ℤ} (hmain : P[pMain]? = some (body pRow))
    (hrow : P[pRow]? = some (rowBody pLookup))
    (hlookup : P[pLookup]? = some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f g lo hi : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nX ≤ dst) (hb : b+nY ≤ dst)
    (hlo : loBase+m ≤ dst) (hhi : hiBase+m ≤ dst)
    (hdst : dst+nX*nY ≤ powers) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((m+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hqueryWord : 2*(U : ℤ) ≤ lim.word)
    (hreadA : ∀ i < nX, μ (a+i) = f i)
    (hreadB : ∀ j < nY, μ (b+j) = g j)
    (hreadLo : ∀ j < m, μ (loBase+j) = lo j)
    (hreadHi : ∀ j < m, μ (hiBase+j) = hi j)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i ≤ j → j < m → lo i ≤ lo j)
    (hm : m < 2^W) (hs : |s| ≤ 1)
    (hf : ∀ i < nX, |f i| ≤ U) (hg : ∀ j < nY, |g j| ≤ U)
    (hd : d+W+3 ≤ lim.depth) :
    Meets lim P pMain d [a,b,loBase,hiBase,nX,nY,m,dst,powers,W,s] μ (time nX nY W)
      (fun _ μ' =>
        (∀ i < nX, ∀ j < nY,
          μ' (dst+i*nY+j) = (rowValue lo hi m (f i) s g j : ℤ)) ∧
        SameOutside μ μ' dst (nX*nY)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for
    (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [a,b,loBase,hiBase,nX,nY,m,dst,powers,W,s,i,r],μ'⟩ ∧
      (∀ j < i, ∀ k < nY,
        μ' (dst+j*nY+k) = (rowValue lo hi m (f j) s g k : ℤ)) ∧
      SameOutside μ μ' dst (nX*nY))
    nX (rowTime nY W+62) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · simp [update_frame_setLocal]
      simpa using (frame_append_zeros [a,b,loBase,hiBase,nX,nY,m,dst,powers,W,s,0] 1).symm
    · intro j hj
      omega
  case round =>
    rintro i _ hin _ ⟨r,μ',rfl,written,kept⟩
    have hiMul : i*nY+nY ≤ nX*nY := by
      have hh := Nat.mul_le_mul_right nY (show i+1 ≤ nX by omega)
      simpa [Nat.add_mul] using hh
    have hiMulLe : i*nY ≤ nX*nY := by omega
    have hiMulNZ : (0 : ℤ) ≤ (i : ℤ)*(nY : ℤ) := by positivity
    have hiAddrWord : (dst : ℤ)+(i : ℤ)*(nY : ℤ) ≤ lim.word := by
      have hz : (dst : ℤ)+(i : ℤ)*(nY : ℤ) ≤ (lim.space : ℤ) := by
        exact_mod_cast (show dst+i*nY ≤ lim.space by omega)
      exact hz.trans hw
    have hrA : μ' (a+i) = f i :=
      (kept (a+i) (Or.inl (by omega))).trans (hreadA i hin)
    have hrB : ∀ j < nY, μ' (b+j) = g j := by
      intro j hj
      exact (kept (b+j) (Or.inl (by omega))).trans (hreadB j hj)
    have hrLo : ∀ j < m, μ' (loBase+j) = lo j := by
      intro j hj
      exact (kept (loBase+j) (Or.inl (by omega))).trans (hreadLo j hj)
    have hrHi : ∀ j < m, μ' (hiBase+j) = hi j := by
      intro j hj
      exact (kept (hiBase+j) (Or.inl (by omega))).trans (hreadHi j hj)
    have hpowers' : Powers μ' powers W := by
      intro j hj
      rw [kept (powers+j) (Or.inr (by omega))]
      exact hpowers j hj
    light_call (row_meets (d := d+1) (x := f i) (s := s) (dst := dst+i*nY)
      hrow hlookup hsearch μ' g lo hi hw (by omega) (by omega) (by omega)
      (by omega) hspace hword hqueryWord hrB hrLo hrHi hpowers' hsorted hm hs
      (hf i hin) hg (by omega))
      using hrA,rowTime,LightBandLookup.time,LightBandLookup.searchTime
      with returned μ'' ⟨rowWritten,rowKept⟩
    refine ⟨by simp,returned,μ'',by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hji : j*nY+nY ≤ i*nY := by
          have hh := Nat.mul_le_mul_right nY (show j+1 ≤ i by omega)
          simpa [Nat.add_mul] using hh
        rw [rowKept (dst+j*nY+k) (Or.inl (by omega))]
        exact written j hj k hk
      · exact rowWritten k hk
    · intro addr haddr
      rw [rowKept addr (by omega)]
      exact kept addr haddr
  case done =>
    rintro _ _ ⟨r,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,μ',rfl,written,kept⟩
    simp

def program : Program :=
  [body 1,rowBody 2,LightBandLookup.body 3,LightBandLookup.searchBody 3]

end ThreeSum.LightBandTable
