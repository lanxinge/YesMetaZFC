import YesMetaZFC.Model.SetTheory.Internal.SmallSkolemSyntax
import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix
import YesMetaZFC.SetTheory.Card.FiniteOrdinal
import YesMetaZFC.SetTheory.Card.OrdinalImage
import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 完整初等嵌入的有限尝试

节点按给定枚举的前若干项记录像。重复编号的一致性、规定的限制图和
全部内部公式的有限赋值真值共同决定节点；不是只检验原子嵌入。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def At_coherent_d (n A B e p : M.Domain) : Prop := ∀ i, M.mem i n → ∀ j, M.mem j n →
  ((∃ x, M.mem x A ∧ Rd_entry_d i x e ∧ Rd_entry_d j x e) ↔
    ∃ y, M.mem y B ∧ Rd_entry_d i y p ∧ Rd_entry_d j y p)

def At_prescribed_d (n A B e τ p : M.Domain) : Prop := ∀ i, M.mem i n →
  ∀ x, M.mem x A → ∀ y, M.mem y B → Rd_entry_d i x e → Rd_entry_d x y τ → Rd_entry_d i y p

def At_elementary_d (ω A R B S e n p : M.Domain) : Prop :=
  ∀ b l F E D q s t, M.mem b ω → Sfm_d I ω l F → Sbound_d I F b →
    M.IsFunctionSpace I E b A → M.IsFunctionSpace I D b B → Fn0_d b n q →
    Cp0_d b ω A q e s → Cp0_d b n B q p t → ∀ r, M.mem r l →
      (Ssat_d I A R E F l r s ↔ Ssat_d I B S D F l r t)

structure At_node_d (ω A R B S e τ n p : M.Domain) : Prop where
  length : M.mem n ω
  function : Fn0_d n B p
  coherent : At_coherent_d n A B e p
  prescribed : At_prescribed_d n A B e τ p
  elementary : At_elementary_d I ω A R B S e n p

variable (hZF : M.Models ZF)
local notation "I₀" => kp_pair_l (ZF.modelsKP hZF)

theorem At_node_d.prefix_l {ω A R B S e τ n m p s : M.Domain}
    (h : At_node_d I₀ ω A R B S e τ m p) (hn : M.mem n ω) (hs : Fn0_d n B s)
    (sub : M.MemberSubset s p) : At_node_d I₀ ω A R B S e τ n s := by
  have res := (Descriptive.ds_restrict_iff_l I₀ (fn0_function_l (ZF.modelsKP hZF) hs)
    (fn0_function_l (ZF.modelsKP hZF) h.function).1).mpr sub
  have hnm : M.MemberSubset n m := fun i hi => by
    obtain ⟨y, _, hiy⟩ := hs.2.1 i hi
    exact (h.function.bound_l ((res.2 i y).mp hiy).2).1
  have entry i y (hi : M.mem i n) : Rd_entry_d i y s ↔ Rd_entry_d i y p :=
    (res.2 i y).trans (and_iff_right hi)
  refine ⟨hn, hs, fun i hi j hj => ?_, fun i hi x hx y hy he hτ => ?_, ?_⟩
  · exact (h.coherent i (hnm i hi) j (hnm j hj)).trans (exists_congr fun y => and_congr_right fun _ =>
      and_congr (entry i y hi).symm (entry j y hj).symm)
  · exact (entry i y hi).mpr (h.prescribed i (hnm i hi) x hx y hy he hτ)
  · intro b l F E D q a t hb hF bound hE hD hq ha ht
    have ht' : Cp0_d b m B q p t := ⟨ht.1, fun i hi => by
      obtain ⟨k, hk, y, hy, hik, hky, hiy⟩ := ht.2 i hi
      exact ⟨k, hnm k hk, y, hy, hik, (entry k y hk).mp hky, hiy⟩⟩
    exact h.elementary b l F E D q a t hb hF bound hE hD (hq.mono_target_l hnm) ha ht'

theorem at_node_of_l {ω c d A R B S j e τ n p : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I₀ c A R) (hn : Smdl_d I₀ d B S)
    (hj : Smap_d I₀ ω c d A B j) (he : Fn0_d ω A e)
    (hτj : ∀ x y, Rd_entry_d x y τ → Rd_entry_d x y j)
    (hnω : M.mem n ω) (hp : Cp0_d n A B e j p) : At_node_d I₀ ω A R B S e τ n p := by
  have maps i x y (hi : M.mem i n) (hex : Rd_entry_d i x e) (hpy : Rd_entry_d i y p) : Rd_entry_d x y j := by
    obtain ⟨a, ha, b, hb, hea, hab, hpb⟩ := hp.2 i hi
    have ex := (fn0_function_l (ZF.modelsKP hZF) he).1.2 i a x hea hex
    have ey := (fn0_function_l (ZF.modelsKP hZF) hp.1).1.2 i b y hpb hpy
    exact ex ▸ ey ▸ hab
  refine ⟨hnω, hp.1, fun i hi k hk => ⟨?_, ?_⟩, fun i hi x _ y _ hex hτ => ?_, ?_⟩
  · rintro ⟨x, _, hix, hkx⟩
    obtain ⟨y, hy, hiy⟩ := hp.1.2.1 i hi
    obtain ⟨z, _, hkz⟩ := hp.1.2.1 k hk
    exact ⟨y, hy, hiy, (hj.1.1.1.2 x z y (maps k x z hk hkx hkz) (maps i x y hi hix hiy)) ▸ hkz⟩
  · rintro ⟨y, _, hiy, hky⟩
    obtain ⟨x, hx, hix⟩ := he.2.1 i (hω.transitive (ZF.modelsKP hZF) n hnω i hi)
    obtain ⟨z, _, hkz⟩ := he.2.1 k (hω.transitive (ZF.modelsKP hZF) n hnω k hk)
    exact ⟨x, hx, hix, (hj.1.2 z x y (maps k z y hk hkz hky) (maps i x y hi hix hiy)) ▸ hkz⟩
  · obtain ⟨z, _, hiz⟩ := hp.1.2.1 i hi
    exact hj.1.1.1.2 x z y (maps i x z hi hex hiz) (hτj x y hτ) ▸ hiz
  · intro b l F E D q s t hb hF bound hE hD hq ha ht r hr
    have mapped : Cp0_d b A B s j t := ⟨ht.1, fun v hv => by
      obtain ⟨i, _, x, hx, hvi, hix, hvx⟩ := ha.2 v hv
      obtain ⟨k, hk, y, hy, hvk, hky, hvy⟩ := ht.2 v hv
      have eq := hq.2.2 v hv k hk i (hq.bound_l hvi).2 hvk hvi
      subst k
      exact ⟨x, hx, y, hy, hvx, maps i x y hk hix hky, hvy⟩⟩
    exact hj.finite_sat_l hZF hω hm hn hb hF bound hr hE hD ha.1 mapped

end YesMetaZFC.SetTheory.Internal

/-! ## 从总尝试枝解码完整初等嵌入

给定可数域的实际编号图，嵌入就是枝沿编号的复合。有限个赋值编号有一个
内部自然数界，所以同一节点能检验任意内部公式；最后恢复原 Smap 证书。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

include hZF in
theorem at_index_bound_l {ω b q : M.Domain} (hω : M.IsOmega ω) (hb : M.mem b ω)
    (hq : Fn0_d b ω q) : ∃ n, M.mem n ω ∧ Fn0_d b n q := by
  have hf := fn0_function_l (ZF.modelsKP hZF) hq
  obtain ⟨D, hD⟩ := ZF.exists_range_of_setFunction hZF I hf.1 hf.2.1
  have fd := hq.retarget_l (fun i x h => (hD x).mpr ⟨i, h⟩)
  have finite : Finite_d I ω D := ⟨b, hb, ZF.ordinal_image_bound_l I hZF ((hω.isOrdinal (ZF.modelsKP hZF)).mem hb)
    (ZF.exists_inclusionInjection hZF I (source := b) (fun _ h => h)) (fn0_function_l (ZF.modelsKP hZF) fd)
    (fun x hx => ((hD x).mp hx).elim fun i hi => ⟨i, (hq.bound_l hi).1, hi⟩)⟩
  have hu : M.IsUnionOf ω ω := fun i => ⟨fun hi => (hω.1.2 i hi).elim fun n hn =>
    ⟨n, hn.2, hn.1.predecessor_mem⟩, fun ⟨n, hn, hi⟩ => hω.transitive (ZF.modelsKP hZF) n hn i hi⟩
  obtain ⟨z, _, hz⟩ := hω.1.1
  obtain ⟨n, hn, sub⟩ := ZF.finite_union_bound_l I hZF hω (hω.isOrdinal (ZF.modelsKP hZF)) hu ⟨z, hz⟩ finite
    (fun x hx => ((hD x).mp hx).elim fun _ hi => (hq.bound_l hi).2)
  exact ⟨n, hn, fd.mono_target_l sub⟩

include hZF in
theorem at_upper_l {ω i k : M.Domain} (hω : M.IsOmega ω) (hi : M.mem i ω) (hk : M.mem k ω) :
    ∃ n, M.mem n ω ∧ M.mem i n ∧ M.mem k n := by
  rcases (hω.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare i hi k hk with eq | hik | hki
  · have eq := hZF.1.eq_of_same_members i k eq
    subst k
    obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
    exact ⟨n, hnω, hn.predecessor_mem, hn.predecessor_mem⟩
  · obtain ⟨n, hn, hnω⟩ := hω.1.2 k hk
    exact ⟨n, hnω, (hn i).mpr (Or.inl hik), hn.predecessor_mem⟩
  · obtain ⟨n, hn, hnω⟩ := hω.1.2 i hi
    exact ⟨n, hnω, hn.predecessor_mem, (hn k).mpr (Or.inl hki)⟩

theorem at_decode_l {ω c d A R B S e τ ι g j : M.Domain}
    (hω : M.IsOmega ω) (hm : Smdl_d I c A R) (hn : Smdl_d I d B S)
    (he : Fn0_d ω A e) (hι : Fn0_d A ω ι)
    (hsect : ∀ x i, Rd_entry_d x i ι → Rd_entry_d i x e)
    (hg : Fn0_d ω B g) (hj : Cp0_d A ω B ι g j)
    (branch : ∀ n, M.mem n ω → ∃ p, At_node_d I ω A R B S e τ n p ∧ M.IsRestrictionOf I p g n) :
    Smap_d I ω c d A B j ∧
      (∀ x y, M.mem x A → M.mem y B → Rd_entry_d x y τ → Rd_entry_d x y j) ∧
      ∀ i x y, Rd_entry_d i x e → Rd_entry_d i y g → Rd_entry_d x y j := by
  have ef := fn0_function_l (ZF.modelsKP hZF) he
  have jf := fn0_function_l (ZF.modelsKP hZF) hj.1
  have maps i x y (hix : Rd_entry_d i x e) (hiy : Rd_entry_d i y g) : Rd_entry_d x y j := by
    obtain ⟨k, hk, hxk⟩ := hι.2.1 x (he.bound_l hix).2
    obtain ⟨n, hn, hin, hkn⟩ := at_upper_l hZF hω (he.bound_l hix).1 hk
    obtain ⟨p, node, res⟩ := branch n hn
    obtain ⟨v, _, hip, hkp⟩ := (node.coherent i hin k hkn).mp ⟨x, (he.bound_l hix).2, hix, hsect x k hxk⟩
    have eq := (fn0_function_l (ZF.modelsKP hZF) hg).1.2 i v y ((res.2 i v).mp hip).2 hiy
    exact (hj.value_l hι hg hxk).mpr (eq ▸ ((res.2 k v).mp hkp).2)
  have inject : M.IsSetInjective I j := by
    intro x z y hxy hzy
    obtain ⟨i, hi, hxi⟩ := hι.2.1 x (hj.1.bound_l hxy).1
    obtain ⟨k, hk, hzk⟩ := hι.2.1 z (hj.1.bound_l hzy).1
    obtain ⟨n, hnω, hin, hkn⟩ := at_upper_l hZF hω hi hk
    obtain ⟨p, node, res⟩ := branch n hnω
    have hip := (res.2 i y).mpr ⟨hin, (hj.value_l hι hg hxi).mp hxy⟩
    have hkp := (res.2 k y).mpr ⟨hkn, (hj.value_l hι hg hzk).mp hzy⟩
    obtain ⟨a, _, hia, hka⟩ := (node.coherent i hin k hkn).mpr ⟨y, (hj.1.bound_l hxy).2, hip, hkp⟩
    exact (ef.1.2 i x a (hsect x i hxi) hia).trans (ef.1.2 k z a (hsect z k hzk) hka).symm
  refine ⟨⟨⟨jf, inject⟩, ?_⟩, (fun x y hx hy hτ => ?_), maps⟩
  · obtain ⟨C, hC⟩ := scode_exists_l I hZF hω
    refine ⟨C, hC, fun a f v ha hf hv assign => ?_⟩
    obtain ⟨l, F, r, code⟩ := (hC a).mp ha
    obtain ⟨b, hb, bound⟩ := sbound_exists_l I hZF hω code.2.1
    have sub := hω.transitive (ZF.modelsKP hZF) b hb
    obtain ⟨s, hs⟩ := ZF.exists_restriction hZF I f b
    obtain ⟨t, ht⟩ := ZF.exists_restriction hZF I v b
    have sf := fn0_of_function_l (ZF.modelsKP hZF) (hs.isSetFunctionFromTo hf sub)
    have tf := fn0_of_function_l (ZF.modelsKP hZF) (ht.isSetFunctionFromTo hv sub)
    obtain ⟨q, hq⟩ := cp0_exists_l (ZF.modelsKP hZF) sf hι
    obtain ⟨n, hnω, qn⟩ := at_index_bound_l hZF hω hb hq.1
    obtain ⟨p, node, res⟩ := branch n hnω
    have source : Cp0_d b ω A q e s := ⟨sf, fun u hu => by
      obtain ⟨x, hx, hux⟩ := sf.2.1 u hu
      obtain ⟨i, hi, hxi⟩ := hι.2.1 x hx
      exact ⟨i, hi, x, hx, (hq.value_l sf hι hux).mpr hxi, hsect x i hxi, hux⟩⟩
    have target : Cp0_d b n B q p t := ⟨tf, fun u hu => by
      obtain ⟨x, hx, hux⟩ := sf.2.1 u hu
      obtain ⟨i, hi, hxi⟩ := hι.2.1 x hx
      obtain ⟨y, hy, hxy⟩ := hj.1.2.1 x hx
      have hui := (hq.value_l sf hι hux).mpr hxi
      have huv := assign u (sub u hu) x y ((hs.2 u x).mp hux).2 hxy
      exact ⟨i, (qn.bound_l hui).2, y, hy, hui,
        (res.2 i y).mpr ⟨(qn.bound_l hui).2, (hj.value_l hι hg hxi).mp hxy⟩, (ht.2 u y).mpr ⟨hu, huv⟩⟩⟩
    obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I b A
    obtain ⟨D, hD⟩ := ZF.exists_functionSpace hZF I b B
    obtain ⟨E₀, hE₀⟩ := ZF.exists_functionSpace hZF I ω A
    obtain ⟨D₀, hD₀⟩ := ZF.exists_functionSpace hZF I ω B
    have left := ssat_spaces_l I hZF (R := R) code.2.1 bound hE₀ hE sub (fun _ h => h) code.2.2
      ((hE₀ f).mpr hf) ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) sf))
      (fun i x hi => ((hs.2 i x).trans (and_iff_right hi)).symm)
    have right := ssat_spaces_l I hZF (R := S) code.2.1 bound hD₀ hD sub (fun _ h => h) code.2.2
      ((hD₀ v).mpr hv) ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) tf))
      (fun i x hi => ((ht.2 i x).trans (and_iff_right hi)).symm)
    exact (satisfies_decode_l I hZF.1 hm code hE₀).trans (left.trans
      ((node.elementary b l F E D q s t hb code.2.1 bound hE hD qn source target r code.2.2).trans
        (right.symm.trans (satisfies_decode_l I hZF.1 hn code hD₀).symm)))
  · obtain ⟨i, hi, hxi⟩ := hι.2.1 x hx
    obtain ⟨n, hni, hnω⟩ := hω.1.2 i hi
    obtain ⟨p, node, res⟩ := branch n hnω
    exact (hj.value_l hι hg hxi).mpr ((res.2 i y).mp
      (node.prescribed i hni.predecessor_mem x hx y hy (hsect x i hxi) hτ)).2

end YesMetaZFC.SetTheory.Internal

/-! ## 尝试节点的原公式

先把一致性、指定限制和双边有限真值检验写成 Δ₀ 公式。
无界量词只选择程序与实际有限真值证书，便于在传递源内逐项读取。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def at_coherent_m {d} (n A B e p : Term d) : Formula 1 d :=
  Formula.forallMem n (Formula.forallMem n.weaken (.iff
    (Formula.existsMem A.weaken.weaken (.conj (rd_entry0_m (.bound 2) .newest e.weaken.weaken.weaken)
      (rd_entry0_m (.bound 1) .newest e.weaken.weaken.weaken)))
    (Formula.existsMem B.weaken.weaken (.conj (rd_entry0_m (.bound 2) .newest p.weaken.weaken.weaken)
      (rd_entry0_m (.bound 1) .newest p.weaken.weaken.weaken)))))
derive_free_closed at_coherent_m

theorem at_coherent_delta_l {d} (n A B e p : Term d) : (at_coherent_m n A B e p).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))
    (.existsMem _ (.conj (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))

theorem at_coherent_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n A B e p : Term d) :
    Formula.satisfies ρ (at_coherent_m n A B e p) ↔
      At_coherent_d (n.eval ρ) (A.eval ρ) (B.eval ρ) (e.eval ρ) (p.eval ρ) := by
  simp only [at_coherent_m, At_coherent_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

def at_prescribed_m {d} (n A B e τ p : Term d) : Formula 1 d :=
  Formula.forallMem n (Formula.forallMem A.weaken (Formula.forallMem B.weaken.weaken
    (.imp (rd_entry0_m (.bound 2) (.bound 1) e.weaken.weaken.weaken)
      (.imp (rd_entry0_m (.bound 1) .newest τ.weaken.weaken.weaken)
        (rd_entry0_m (.bound 2) .newest p.weaken.weaken.weaken)))))
derive_free_closed at_prescribed_m

theorem at_prescribed_delta_l {d} (n A B e τ p : Term d) : (at_prescribed_m n A B e τ p).IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.imp (rd_entry0_delta_l ..)
    (.imp (rd_entry0_delta_l ..) (rd_entry0_delta_l ..)))))

theorem at_prescribed_sat_l (hE : Extensional M) {d} (ρ : Env M d) (n A B e τ p : Term d) :
    Formula.satisfies ρ (at_prescribed_m n A B e τ p) ↔
      At_prescribed_d (n.eval ρ) (A.eval ρ) (B.eval ρ) (e.eval ρ) (τ.eval ρ) (p.eval ρ) := by
  simp only [at_prescribed_m, At_prescribed_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def At_test_d (ω A B e n p Q b l E D C H C' H' : M.Domain) : Prop :=
  ∀ r, M.mem r l → ∀ q, M.mem q Q → ∀ s, M.mem s E → ∀ t, M.mem t D →
    Fn0_d b n q → Cp0_d b ω A q e s → Cp0_d b n B q p t →
      (Fv_at_d C H r s ↔ Fv_at_d C' H' r t)

def at_test_m {d} (ω A B e n p Q b l E D C H C' H' : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken
  Formula.forallMem l (Formula.forallMem Q.weaken (Formula.forallMem E.weaken.weaken
    (Formula.forallMem D.weaken.weaken.weaken (.imp (fn0_m (w b) (w n) (.bound 2))
      (.imp (cp0_m (w b) (w ω) (w A) (.bound 2) (w e) (.bound 1))
        (.imp (cp0_m (w b) (w n) (w B) (.bound 2) (w p) .newest)
          (.iff (fv_at_m (w C) (w H) (.bound 3) (.bound 1)) (fv_at_m (w C') (w H') (.bound 3) .newest))))))))
derive_free_closed at_test_m

theorem at_test_delta_l {d} (ω A B e n p Q b l E D C H C' H' : Term d) :
    (at_test_m ω A B e n p Q b l E D C H C' H').IsDelta0 :=
  .forallMem _ (.forallMem _ (.forallMem _ (.forallMem _ (.imp (fn0_delta_l ..)
    (.imp (cp0_delta_l ..) (.imp (cp0_delta_l ..) (.iff (fv_at_delta_l ..) (fv_at_delta_l ..))))))))

theorem at_test_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A B e n p Q b l E D C H C' H' : Term d) :
    Formula.satisfies ρ (at_test_m ω A B e n p Q b l E D C H C' H') ↔ At_test_d
      (ω.eval ρ) (A.eval ρ) (B.eval ρ) (e.eval ρ) (n.eval ρ) (p.eval ρ) (Q.eval ρ) (b.eval ρ)
      (l.eval ρ) (E.eval ρ) (D.eval ρ) (C.eval ρ) (H.eval ρ) (C'.eval ρ) (H'.eval ρ) := by
  simp only [at_test_m, At_test_d, Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff,
    fn0_sat_l hE, cp0_sat_l hE, Formula.satisfies_iff_iff, fv_at_sat_l hE,
    Definitional.Term.eval_weaken]; rfl

def At_cert_d (hKP : M.Models KP) (ω A R B S e n p Q J K b l L F E D C H C' H' : M.Domain) : Prop :=
  Fv_space_d b A J E ∧ Fv_space_d b B K D ∧ Fv_eval_d hKP b A R E l L F C H ∧
    Fv_eval_d hKP b B S D l L F C' H' ∧ At_test_d ω A B e n p Q b l E D C H C' H'

def at_cert_m {d} (ω A R B S e n p Q J K b l L F E D C H C' H' : Term d) : Formula 1 d :=
  .conj (fv_space_m b A J E) (.conj (fv_space_m b B K D) (.conj (fv_eval_m b A R E l L F C H)
    (.conj (fv_eval_m b B S D l L F C' H') (at_test_m ω A B e n p Q b l E D C H C' H'))))
derive_free_closed at_cert_m

theorem at_cert_delta_l {d} (ω A R B S e n p Q J K b l L F E D C H C' H' : Term d) :
    (at_cert_m ω A R B S e n p Q J K b l L F E D C H C' H').IsDelta0 :=
  .conj (fv_space_delta_l ..) (.conj (fv_space_delta_l ..) (.conj (fv_eval_delta_l ..)
    (.conj (fv_eval_delta_l ..) (at_test_delta_l ..))))

theorem at_cert_sat_l (hKP : M.Models KP) {d} (ρ : Env M d)
    (ω A R B S e n p Q J K b l L F E D C H C' H' : Term d) :
    Formula.satisfies ρ (at_cert_m ω A R B S e n p Q J K b l L F E D C H C' H') ↔ At_cert_d hKP
      (ω.eval ρ) (A.eval ρ) (R.eval ρ) (B.eval ρ) (S.eval ρ) (e.eval ρ) (n.eval ρ) (p.eval ρ)
      (Q.eval ρ) (J.eval ρ) (K.eval ρ) (b.eval ρ) (l.eval ρ) (L.eval ρ) (F.eval ρ)
      (E.eval ρ) (D.eval ρ) (C.eval ρ) (H.eval ρ) (C'.eval ρ) (H'.eval ρ) := by
  simp only [at_cert_m, At_cert_d, Formula.satisfies_conj_iff, fv_space_sat_l hKP.1,
    fv_eval_sat_l hKP, at_test_sat_l hKP.1]

/-- 六个见证都是可检验的集合与函数图。 -/
def at_witness_m {d} (ω A R B S e n p Q J K b l L F : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken.weaken.weaken
  .existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (at_cert_m (w ω) (w A) (w R) (w B) (w S) (w e) (w n) (w p) (w Q) (w J) (w K)
      (w b) (w l) (w L) (w F) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest))))))
derive_free_closed at_witness_m

def at_elementary_m {d} (ω A R B S e n p Q J K : Term d) : Formula 1 d :=
  let w (t : Term d) := t.weaken.weaken.weaken.weaken
  .forallE (.forallE (.forallE (.forallE (.imp (fb_program_m (w ω) (.bound 3) (.bound 2) (.bound 1) .newest)
    (at_witness_m (w ω) (w A) (w R) (w B) (w S) (w e) (w n) (w p) (w Q) (w J) (w K)
      (.bound 3) (.bound 2) (.bound 1) .newest)))))
derive_free_closed at_elementary_m

def at_node_m {d} (ω A R B S e τ p Q J K : Term d) : Formula 1 d :=
  Formula.existsMem ω (.conj (fn0_m .newest B.weaken p.weaken)
    (.conj (at_coherent_m .newest A.weaken B.weaken e.weaken p.weaken)
      (.conj (at_prescribed_m .newest A.weaken B.weaken e.weaken τ.weaken p.weaken)
        (at_elementary_m ω.weaken A.weaken R.weaken B.weaken S.weaken e.weaken .newest p.weaken Q.weaken J.weaken K.weaken))))
derive_free_closed at_node_m

end YesMetaZFC.SetTheory.Internal

/-! ## 完整初等性检验与有限真值证书

全部内部程序均有实际有限值域与真值表；证书检验精确恢复原满足关系。
此等价供联合尝试节点使用，与传递源中的证书读取共用同一原公式。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem at_elementary_sat_l {d} (ρ : Env M d) (ω A R B S e n p Q J K : Term d)
    (hω : M.IsOmega (ω.eval ρ)) (hn : M.mem (n.eval ρ) (ω.eval ρ))
    (hQ : Fseq_space_d I (ω.eval ρ) (ω.eval ρ) (Q.eval ρ))
    (hJ : Fseq_space_d I (ω.eval ρ) (A.eval ρ) (J.eval ρ))
    (hK : Fseq_space_d I (ω.eval ρ) (B.eval ρ) (K.eval ρ)) :
    Formula.satisfies ρ (at_elementary_m ω A R B S e n p Q J K) ↔
      At_elementary_d I (ω.eval ρ) (A.eval ρ) (R.eval ρ) (B.eval ρ) (S.eval ρ)
        (e.eval ρ) (n.eval ρ) (p.eval ρ) := by
  simp only [at_elementary_m, at_witness_m, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_exists_iff, fb_program_sat_l (ZF.modelsKP hZF),
    at_cert_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  constructor
  · intro h b l F E D q s t hb hF bound hE hD hq hs ht r hr
    obtain ⟨L, range⟩ := ZF.exists_range_of_setFunction hZF I hF.2.1.2.1 hF.2.1.2.2
    have fn : Fn0_d l L F := fn0_of_function_l (ZF.modelsKP hZF)
      ⟨hF.2.1.2.1, hF.2.1.2.2, fun a ha => ((hF.2.1.2.2 a).mp ha).imp
        fun x hx => ⟨(range x).mpr ⟨a, hx⟩, hx⟩⟩
    have program := fb_program_of_l (ZF.modelsKP hZF) hF hb bound fn
    obtain ⟨E', D', C, H, C', H', space, space', ev, ev', test⟩ := h b l L F program
    have eqE := hZF.1.eq_of_same_members E' E (fun f =>
      ((fv_space_l (ZF.modelsKP hZF) hb hJ).mp space f).trans (hE f).symm)
    have eqD := hZF.1.eq_of_same_members D' D (fun f =>
      ((fv_space_l (ZF.modelsKP hZF) hb hK).mp space' f).trans (hD f).symm)
    subst E' D'
    exact (ev.truth_l hZF hω program hE hr).symm.trans
      ((test r hr q ((hQ q).mpr ⟨b, hb, fn0_function_l (ZF.modelsKP hZF)
        (hq.mono_target_l (hω.transitive (ZF.modelsKP hZF) _ hn))⟩)
        s ((hE s).mpr (fn0_function_l (ZF.modelsKP hZF) hs.1))
        t ((hD t).mpr (fn0_function_l (ZF.modelsKP hZF) ht.1)) hq hs ht).trans
          (ev'.truth_l hZF hω program hD hr))
  · intro h b l L F program
    obtain ⟨hF, bound⟩ := program.read_l hZF hω
    have evaluate A R : ∃ E C H, M.IsFunctionSpace I E b A ∧
        Fv_eval_d (ZF.modelsKP hZF) b A R E l L F C H := by
      obtain ⟨E, space⟩ := ZF.exists_functionSpace hZF I b A
      obtain ⟨H, ev⟩ := seval_exists_l I hZF A R E F hF.2.1.1
      obtain ⟨C, range⟩ := ZF.exists_range_of_setFunction hZF I ev.1.2.1 ev.1.2.2
      exact ⟨E, C, H, space, fv_eval_of_l hZF hω program space ev
        (fn0_of_function_l (ZF.modelsKP hZF) ⟨ev.1.2.1, ev.1.2.2, fun a ha =>
          ((ev.1.2.2 a).mp ha).imp fun x hx => ⟨(range x).mpr ⟨a, hx⟩, hx⟩⟩)⟩
    obtain ⟨E, C, H, space, ev⟩ := evaluate (A.eval ρ) (R.eval ρ)
    obtain ⟨D, C', H', space', ev'⟩ := evaluate (B.eval ρ) (S.eval ρ)
    refine ⟨E, D, C, H, C', H', (fv_space_l (ZF.modelsKP hZF) program.1 hJ).mpr space,
      (fv_space_l (ZF.modelsKP hZF) program.1 hK).mpr space', ev, ev', fun r hr q _ s _ t _ hq hs ht => ?_⟩
    exact (ev.truth_l hZF hω program space hr).trans
      ((h b l F E D q s t program.1 hF bound space space' hq hs ht r hr).trans
        (ev'.truth_l hZF hω program space' hr).symm)

end YesMetaZFC.SetTheory.Internal

/-! ## 尝试公式在传递源中的读取

程序与真值表的矩阵均为 Δ₀。外层无界量词保留为源内对象量词，
不把源的任意公式真值误当成背景真值。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def At_relative_d (hKP : M.Models KP) (Z ω A R B S e n p Q J K : M.Domain) : Prop :=
  ∀ b l L F, M.mem b Z → M.mem l Z → M.mem L Z → M.mem F Z → Fb_program_d hKP ω b l L F →
    ∃ E D C H C' H', M.mem E Z ∧ M.mem D Z ∧ M.mem C Z ∧ M.mem H Z ∧ M.mem C' Z ∧ M.mem H' Z ∧
      At_cert_d hKP ω A R B S e n p Q J K b l L F E D C H C' H'

theorem at_relative_sat_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x : M.Domain // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d)
    (ω A R B S e n p Q J K : Term d) :
    Formula.satisfies ρ (at_elementary_m ω A R B S e n p Q J K) ↔ At_relative_d hKP Z
      (ω.eval ρ).val (A.eval ρ).val (R.eval ρ).val (B.eval ρ).val (S.eval ρ).val (e.eval ρ).val
      (n.eval ρ).val (p.eval ρ).val (Q.eval ρ).val (J.eval ρ).val (K.eval ρ).val := by
  have prog {a} (η : Env (rt_model_l Z hz) a) (ω b l L F : Term a) :
      Formula.satisfies η (fb_program_m ω b l L F) ↔ Fb_program_d hKP
        (ω.eval η).val (b.eval η).val (l.eval η).val (L.eval η).val (F.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ hz (fb_program_delta_l ω b l L F) η).trans (fb_program_sat_l hKP ..)
  have cert {a} (η : Env (rt_model_l Z hz) a) (ω A R B S e n p Q J K b l L F E D C H C' H' : Term a) :
      Formula.satisfies η (at_cert_m ω A R B S e n p Q J K b l L F E D C H C' H') ↔ At_cert_d hKP
        (ω.eval η).val (A.eval η).val (R.eval η).val (B.eval η).val (S.eval η).val (e.eval η).val
        (n.eval η).val (p.eval η).val (Q.eval η).val (J.eval η).val (K.eval η).val
        (b.eval η).val (l.eval η).val (L.eval η).val (F.eval η).val (E.eval η).val (D.eval η).val
        (C.eval η).val (H.eval η).val (C'.eval η).val (H'.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ hz (at_cert_delta_l ω A R B S e n p Q J K b l L F E D C H C' H') η).trans (at_cert_sat_l hKP ..)
  simp only [at_elementary_m, at_witness_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_exists_iff, prog, cert, Definitional.Term.eval_weaken]
  constructor
  · intro h b l L F hb hl hL hF hp
    obtain ⟨E, D, C, H, C', H', cert⟩ := h ⟨b, hb⟩ ⟨l, hl⟩ ⟨L, hL⟩ ⟨F, hF⟩ hp
    exact ⟨E.val, D.val, C.val, H.val, C'.val, H'.val,
      E.property, D.property, C.property, H.property, C'.property, H'.property, cert⟩
  · intro h b l L F hp
    obtain ⟨E, D, C, H, C', H', hE, hD, hC, hH, hC', hH', cert⟩ :=
      h b.val l.val L.val F.val b.property l.property L.property F.property hp
    exact ⟨⟨E, hE⟩, ⟨D, hD⟩, ⟨C, hC⟩, ⟨H, hH⟩, ⟨C', hC'⟩, ⟨H', hH'⟩, cert⟩

theorem at_node_relative_l (hKP : M.Models KP) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (hz : Nonempty {x : M.Domain // M.mem x Z}) {d} (ρ : Env (rt_model_l Z hz) d)
    (ω A R B S e τ p Q J K : Term d) : Formula.satisfies ρ (at_node_m ω A R B S e τ p Q J K) ↔
    ∃ n, M.mem n (ω.eval ρ).val ∧ Fn0_d n (B.eval ρ).val (p.eval ρ).val ∧
      At_coherent_d n (A.eval ρ).val (B.eval ρ).val (e.eval ρ).val (p.eval ρ).val ∧
      At_prescribed_d n (A.eval ρ).val (B.eval ρ).val (e.eval ρ).val (τ.eval ρ).val (p.eval ρ).val ∧
      At_relative_d hKP Z (ω.eval ρ).val (A.eval ρ).val (R.eval ρ).val (B.eval ρ).val (S.eval ρ).val
        (e.eval ρ).val n (p.eval ρ).val (Q.eval ρ).val (J.eval ρ).val (K.eval ρ).val := by
  have basic (n : (rt_model_l Z hz).Domain) :
      Formula.satisfies (ρ.push n) (.conj (fn0_m .newest B.weaken p.weaken)
        (.conj (at_coherent_m .newest A.weaken B.weaken e.weaken p.weaken)
          (at_prescribed_m .newest A.weaken B.weaken e.weaken τ.weaken p.weaken))) ↔
        Fn0_d n.val (B.eval ρ).val (p.eval ρ).val ∧
          At_coherent_d n.val (A.eval ρ).val (B.eval ρ).val (e.eval ρ).val (p.eval ρ).val ∧
          At_prescribed_d n.val (A.eval ρ).val (B.eval ρ).val (e.eval ρ).val (τ.eval ρ).val (p.eval ρ).val := by
    have h := rt_model_delta_l hZ hz (.conj (fn0_delta_l .newest B.weaken p.weaken)
      (.conj (at_coherent_delta_l .newest A.weaken B.weaken e.weaken p.weaken)
        (at_prescribed_delta_l .newest A.weaken B.weaken e.weaken τ.weaken p.weaken))) (ρ.push n)
    simpa only [Formula.satisfies_conj_iff, fn0_sat_l hKP.1, at_coherent_sat_l hKP.1,
      at_prescribed_sat_l hKP.1, eval_image_env_l (M := rt_model_l Z hz) (N := M) Subtype.val, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using h
  simp only [Formula.satisfies_conj_iff] at basic
  simp only [at_node_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    at_relative_sat_l hKP hZ hz, Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨n, hn, hf, hc, hp, he⟩
    obtain ⟨hf, hc, hp⟩ := (basic n).mp ⟨hf, hc, hp⟩
    exact ⟨n.val, hn, hf, hc, hp, he⟩
  · rintro ⟨n, hn, hf, hc, hp, he⟩
    let v : (rt_model_l Z hz).Domain := ⟨n, hZ _ (ω.eval ρ).property n hn⟩
    obtain ⟨hf, hc, hp⟩ := (basic v).mpr ⟨hf, hc, hp⟩
    exact ⟨v, hn, hf, hc, hp, he⟩

end YesMetaZFC.SetTheory.Internal
