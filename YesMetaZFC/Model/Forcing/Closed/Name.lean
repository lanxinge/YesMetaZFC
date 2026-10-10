import YesMetaZFC.Model.Forcing.Closed.Sequence

/-! # 被迫可数闭偏序中的同条件下界名称

先装配整条内部名称链，再在原条件上消去闭性并使用最大值原理。
逐项读取装配序列，使所选下界同时满足全部旧指标，原条件不作加强。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z : M.Domain}

theorem nchain_bound_name_l (O : Cond_order_d M B R z) (hZFC : M.Models ZFC)
    {b p ω A T f t w} (hb : M.mem b B) (hp : Below_d M B R z p b)
    (hf : Nchain_d (kpair_interpretation_l M hZFC.1 (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC))))
      B R z p ω A T f) (ht : Nseq_d M B b f t) (hw : Check_d M b ω w)
    (hA : Name_d M B A) (hT : Name_d M B T)
    (hc : Forces_d M B R z (closed_m (.bound 1) .newest (.bound 1) (.bound 2))
      (((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T) p) :
    ∃ q, Name_d M B q ∧ Mem_force_d M B R z p q A ∧
      ∀ i s, Entry_d M i s f → Rel_force_d M B R z T p q s := by
  have hZF := ZFC.models_zf_l hZFC
  have hwN := check_name_l M (check_range_l M hZF) hb hw
  let η : Env M 3 := ((⟨fun _ => w, fun _ => w⟩ : Env M 1).push A).push T
  let ρ := η.push t
  have push {n} {δ : Env M n} {s} (hs : Name_d M B s)
      (hd : ∀ a : Term n, Name_d M B (a.eval δ)) : ∀ a : Term (n+1), Name_d M B (a.eval (δ.push s)) := by
    intro a
    cases a with
    | free i => exact hd (.free i)
    | bound i => exact Fin.cases hs (fun i => hd (.bound i)) i
  have hη : ∀ a : Term 3, Name_d M B (a.eval η) := by
    intro a
    cases a with
    | free _ => exact hwN
    | bound i => exact Fin.cases hT (Fin.cases hA (fun _ => hwN)) i
  have hρ := push ht.1 hη
  let φ : Formula 1 4 := chain_m (.bound 2) (.bound 1) (.bound 2) (.bound 3) .newest
  let ψ : UnarySchema 4 := { body := chain_bound_m (.bound 3) (.bound 2) (.bound 3) (.bound 1) .newest }
  have hchain : Forces_d M B R z φ ρ p := nchain_force_l O hZF hb hp hf ht hw hA hT
  have hArrow : Forces_d M B R z (.imp φ (.existsE ψ.body)) ρ p := (forces_all_l hZF.1 _ η p).mp hc t ht.1
  have hex := forces_mp_l hZF.1 (forces_regular_l O hZF φ ρ hρ).1
    (forces_regular_l O hZF (.existsE ψ.body) ρ hρ) hp.1 hp.2.1 hArrow hchain
  obtain ⟨q, hq, _, hmax⟩ := maximum_l O hZFC ψ ρ (fun i => hρ (.bound i))
  have hbound := (hmax p hp.1 hp.2.1).mp hex
  have hqA := (forces_mem_l hZF.1 .newest (.bound 3) (ρ.push q) p).mp ((forces_conj_l _ _ _ p).mp hbound).1
  refine ⟨q, hq, hqA, fun i s his => ?_⟩
  obtain ⟨c, hic, hcN, _⟩ := zf_check_l M hZF hb i
  have hs := (hf.2.2.1 i s his).1
  have hcs := nseq_entry_force_l O hZF hb ht hic hs his hp
  have hall := ((forces_conj_l _ _ _ p).mp ((forces_conj_l _ _ _ p).mp hbound).2).2
  let ξ := ((ρ.push q).push c).push s
  have hξ := push hs (push hcN (push hq hρ))
  have hArrow := (forces_all_l hZF.1 _ _ p).mp ((forces_all_l hZF.1 _ _ p).mp hall c hcN) s hs
  have he : Forces_d M B R z (entry_m (.bound 1) .newest (.bound 3)) ξ p :=
    (force_entry_l hZF.1 ξ p (.bound 1) .newest (.bound 3)).mpr hcs
  exact (force_entry_l hZF.1 ξ p (.bound 2) .newest (.bound 4)).mp
    (forces_mp_l hZF.1 (forces_regular_l O hZF _ ξ hξ).1 (forces_regular_l O hZF _ ξ hξ)
      hp.1 hp.2.1 hArrow he)

end YesMetaZFC.Model.Forcing.Internal
