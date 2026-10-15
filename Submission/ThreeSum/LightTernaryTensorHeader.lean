import Submission.ThreeSum.LightTernaryTensorDriverSyntax

namespace ThreeSum.LightTernaryTensorHeader
open Light LightTernaryTensorDriver

theorem args_safe {lim : Limits} (σ : State) (config : ℕ)
    (hconfig : σ.loc 0=(config : ℤ))
    (hspace : config+106≤lim.space) (hw : (lim.space : ℤ)≤lim.word) :
    ∀ e∈countArgs, e.Safe lim σ := by
  intro e he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
  have hi' : i<106 := List.mem_range.mp hi
  simp only [Expr.Safe,Expr.val,Op.eval,hconfig]
  have hix : (i : ℤ)≤lim.word := by
    have hh : (i : ℤ)≤lim.space := by exact_mod_cast (by omega : i≤lim.space)
    omega
  have haddr : (config : ℤ)+(i : ℤ)<lim.space := by exact_mod_cast (by omega : config+i<lim.space)
  have hnon : 0≤(config : ℤ)+(i : ℤ) := by positivity
  exact ⟨⟨trivial,hix,(abs_of_nonneg hnon).symm ▸ (by omega)⟩,hnon,haddr⟩

theorem args_values (σ : State) (config : ℕ) (vals : List ℤ)
    (hconfig : σ.loc 0=(config : ℤ)) (hlen : vals.length=106)
    (hread : ∀ i<106, σ.mem (config+i)=vals.getD i 0) :
    countArgs.map (·.val σ)=vals := by
  apply List.ext_getElem (by simp [countArgs,hlen])
  intro i hi hi'
  have hir : i<106 := by simpa [countArgs] using hi
  have hr := hread i hir
  simpa [countArgs,Expr.val,Op.eval,hconfig,List.getD,List.getElem?_eq_getElem hi'] using hr

@[simp] theorem args_cost : (countArgs.map Expr.cost).sum=424 := by
  simp [countArgs,List.map_map,Function.comp_def,M,v,k,Expr.cost,List.map_const,List.sum_replicate]

end ThreeSum.LightTernaryTensorHeader
