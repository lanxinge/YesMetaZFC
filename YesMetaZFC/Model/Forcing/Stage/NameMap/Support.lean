import YesMetaZFC.Model.Forcing.Stage.NameMap.Construction

/-! # 名字搬运只需控制原闭支撑上的标签

将实际搬运图限制到原名字的闭支撑，其像给出目标名字的闭支撑。
标签关系在其他条件上的行为无关，供有限前缀名字的统一补长使用。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
include hZF

theorem nmap_support_name_l {P Q K x t : M.Domain}
    (bound : ∀ p q, M.mem p P → Entry_d M p q K → M.mem q Q)
    (name : Name_d M P x) (map : Nmap_d M K x t) : Name_d M Q t := by
  obtain ⟨S,hx,supp⟩ := name
  obtain ⟨H,graph,xt⟩ := map
  obtain ⟨V,range⟩ := check_range_l M hZF H
  let ρ : Env M 2 := ⟨Fin.cases S (fun _ => H),fun _ => x⟩
  let φ : UnarySchema 2 := { body := Formula.existsMem (.bound 1) (entry_m .newest (.bound 1) (.bound 3)) }
  obtain ⟨W,sep⟩ := ZF.separation_exists_d hZF φ ρ V
  have read y : M.mem y W ↔ ∃ s, M.mem s S ∧ Entry_d M s y H := by
    have sat : φ.denote ρ y ↔ ∃ s, M.mem s S ∧ Entry_d M s y H := by
      simp only [φ,UnarySchema.denote,Formula.satisfies_existsMem_iff,entry_sat_l M hZF.1]
      rfl
    exact (sep y).trans ⟨fun h => sat.mp h.2,fun ⟨s,hs,sy⟩ => ⟨(range y).mpr ⟨s,sy⟩,sat.mpr ⟨s,hs,sy⟩⟩⟩
  refine ⟨W,(read t).mpr ⟨x,hx,xt⟩,?_⟩
  intro y hy v hv
  obtain ⟨s,hs,sy⟩ := (read y).mp hy
  obtain ⟨a,p,b,q,ap,ab,pq,pair⟩ := ((graph.2 s y sy).2 v).mp hv
  have old := supp_entry_l M supp hs ap
  exact ⟨b,q,pair,(read b).mpr ⟨a,old.1,ab⟩,bound p q old.2 pq⟩

end YesMetaZFC.Model.Forcing.Internal
