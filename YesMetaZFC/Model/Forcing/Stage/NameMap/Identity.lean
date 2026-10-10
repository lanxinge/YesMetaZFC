import YesMetaZFC.Model.Forcing.Stage.NameMap.Construction

/-! # 恒等搬运与零标签消去

正条件上的恒等图会删除零标签。用名称搬运关系直接构造内部双模拟，证明
搬运结果与原名称在每个条件上被迫相等，无需假定零条件不属于条件集。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}} {B R z F : M.Domain}

/-- 保留全部标签的恒等图逐对象固定名称；闭支撑上的对角图就是递归证书。 -/
theorem nmap_identity_l (hZF : M.Models ZF)
    (hF : ∀ b c, Entry_d M b c F ↔ M.mem b B ∧ c = b) {x} (hx : Name_d M B x) : Nmap_d M F x x := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨S, hx, hS⟩ := hx
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => B⟩
  let φ : BinarySchema 0 := { body := Formula.extensionalEq .newest (.bound 1) }
  obtain ⟨H, hH, hH'⟩ := ZF.exists_setRelationOn_of_denote hZF I φ ρ S
  have he s t : Entry_d M s t H ↔ M.mem s S ∧ t = s := by
    refine (hH' s t).trans ?_
    have hφ : φ.denote ρ s t ↔ t = s := Formula.satisfies_extensionalEq_iff_eq hZF.1 _ _ _
    rw [hφ]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun ⟨hs, ht⟩ => ⟨hs, ht.symm ▸ hs, ht⟩⟩
  refine ⟨H, ⟨hH.1, fun s t hst => ?_⟩, (he x x).mpr ⟨hx, rfl⟩⟩
  obtain ⟨hs, hts⟩ := (he s t).mp hst
  subst t
  refine ⟨fun a b hab => ⟨a, (he a a).mpr ⟨(supp_entry_l M hS hs hab).1, rfl⟩⟩, fun v => ?_⟩
  constructor
  · intro hv
    obtain ⟨a, b, hvab, ha, hb⟩ := hS s hs v hv
    exact ⟨a, b, a, b, ⟨v, hvab, hv⟩, (he a a).mpr ⟨ha, rfl⟩, (hF b b).mpr ⟨hb, rfl⟩, hvab⟩
  · rintro ⟨a, b, c, d, hab, hac, hbd, hv⟩
    have hc := ((he a c).mp hac).2
    have hd := ((hF b d).mp hbd).2
    subst c d
    obtain ⟨w, hw, hws⟩ := hab
    exact kpair_unique_l M hZF.1 hw hv ▸ hws

theorem nmap_id_force_l (O : Cond_order_d M B R z) (hZF : M.Models ZF)
    (hF : ∀ b c, Entry_d M b c F ↔ M.mem b B ∧ b ≠ z ∧ c = b)
    {x t p} (hx : Name_d M B x) (ht : Nmap_d M F x t) (hp : M.mem p B) :
    Eq_force_d M B R z p x t := by
  let hI : Mem_ind_d M := check_ind_l M hZF
  let hP := KP.exists_pair (ZF.modelsKP hZF)
  have htN := nmap_name_l M hZF (fun b c hc => by
    obtain ⟨hb, _, he⟩ := (hF b c).mp hc
    exact he.symm ▸ hb) ht
  obtain ⟨S, hxS, htS, hS⟩ := name_support_l M hP (KP.exists_union (ZF.modelsKP hZF)) hx htN
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : BinarySchema 2 := { body := nmap_m (.bound 3) (.bound 1) .newest }
  obtain ⟨K, hK⟩ := rel_separation_l hZF φ ρ B S
  have hk q s u : Rel_d M K q s u ↔ M.mem q B ∧ M.mem s S ∧ M.mem u S ∧ Nmap_d M F s u := by
    simpa only [BinarySchema.denote, φ, nmap_sat_l M hZF.1] using! hK q s u
  refine ⟨hp, K, ?_, (hk p x t).mpr ⟨hp, hxS, htS, ht⟩⟩
  intro q s u h
  obtain ⟨_, hs, hu, hm⟩ := (hk q s u).mp h
  constructor
  · intro a b hab r hr hrb
    have hb := (supp_entry_l M hS hs hab).2
    have hbz : b ≠ z := fun he => hr.2.1 (O.zero r hr.1 (he ▸ hrb))
    obtain ⟨a', ha⟩ := nmap_exists_l M hZF F a
    have ha'u := (nmap_entry_l M hZF.1 hI hP hm a' b).mpr ⟨a, b, hab, ha, (hF b b).mpr ⟨hb, hbz, rfl⟩⟩
    exact ⟨r, a', b, below_refl_l O hr.1 hr.2.1, ha'u, hrb,
      (hk r a a').mpr ⟨hr.1, (supp_entry_l M hS hs hab).1, (supp_entry_l M hS hu ha'u).1, ha⟩⟩
  · intro a b hab r hr hrb
    obtain ⟨c, d, hcd, hca, hdb⟩ := (nmap_entry_l M hZF.1 hI hP hm a b).mp hab
    have he : b = d := ((hF d b).mp hdb).2.2
    exact ⟨r, c, d, below_refl_l O hr.1 hr.2.1, hcd, he ▸ hrb,
      (hk r c a).mpr ⟨hr.1, (supp_entry_l M hS hs hcd).1, (supp_entry_l M hS hu hab).1, hca⟩⟩

end YesMetaZFC.Model.Forcing.Internal
