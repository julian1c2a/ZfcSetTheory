import ZFC.Rat.Field

namespace ZFC.Rat.Field

  universe u
  variable {U : Type u}

  theorem test_mul (a b c : U)
      (ha : a ∈ (RatSet : U)) (hb : b ∈ (RatSet : U)) (hc : c ∈ (RatSet : U))
      (h_le : leQ a b) (h_c_nn : leQ (zeroQ : U) c) :
      leQ (mulQ a c) (mulQ b c) := by
    obtain ⟨a_num, a_den, ha_num, ha_den, ha_eq⟩ := mem_RatSet_is_ratClass a ha
    obtain ⟨b_num, b_den, hb_num, hb_den, hb_eq⟩ := mem_RatSet_is_ratClass b hb
    obtain ⟨c_num, c_den, hc_num, hc_den, hc_eq⟩ := mem_RatSet_is_ratClass c hc
    have ha_den_i := NonZeroIntSet_mem_IntSet a_den ha_den
    have hb_den_i := NonZeroIntSet_mem_IntSet b_den hb_den
    have hc_den_i := NonZeroIntSet_mem_IntSet c_den hc_den
    have H_ab := h_le a_num a_den b_num b_den ha_num ha_den hb_num hb_den ha_eq hb_eq
    have H_c := h_c_nn zeroZ oneZ c_num c_den zeroZ_mem_IntSet oneZ_mem_NonZeroIntSet hc_num hc_den rfl hc_eq
    unfold leQ_repr at H_ab H_c
    rw [mulZ_zero_left oneZ oneZ_mem_IntSet,
        mulZ_zero_left (mulZ c_den c_den) (mulZ_in_IntSet c_den c_den hc_den_i hc_den_i),
        mulZ_one_left oneZ oneZ_mem_IntSet,
        mulZ_one_left (mulZ c_num c_den) (mulZ_in_IntSet c_num c_den hc_num hc_den_i)] at H_c

    rw [ha_eq, hb_eq, hc_eq,
        mulQ_class a_num a_den c_num c_den ha_num ha_den hc_num hc_den,
        mulQ_class b_num b_den c_num c_den hb_num hb_den hc_num hc_den]
    intro a' b' c' d' ha' hb' hc' hd' hac_eq hbc_eq
    have h1 : ratClass (mulZ a_num c_num) (mulZ a_den c_den) = ratClass a' b' := by rw [← hac_eq]
    have h2 : ratClass (mulZ b_num c_num) (mulZ b_den c_den) = ratClass c' d' := by rw [← hbc_eq]
    apply (leQ_repr_well_defined
             (mulZ a_num c_num) (mulZ a_den c_den) a' b'
             (mulZ b_num c_num) (mulZ b_den c_den) c' d'
             (mulZ_in_IntSet a_num c_num ha_num hc_num)
             (mulZ_in_NonZeroIntSet a_den c_den ha_den hc_den)
             ha' hb'
             (mulZ_in_IntSet b_num c_num hb_num hc_num)
             (mulZ_in_NonZeroIntSet b_den c_den hb_den hc_den)
             hc' hd' h1 h2).mp
    unfold leQ_repr

    have hc_num_den := mulZ_in_IntSet c_num c_den hc_num hc_den_i
    have hc_den_sq := mulZ_in_IntSet c_den c_den hc_den_i hc_den_i
    have hc_mul := mulZ_in_IntSet (mulZ c_num c_den) (mulZ c_den c_den) hc_num_den hc_den_sq
    
    have hc_mul_nn : leZ (zeroZ : U) (mulZ (mulZ c_num c_den) (mulZ c_den c_den)) := by
      have step := mulZ_le_mulZ_nonneg zeroZ (mulZ c_num c_den) (mulZ c_den c_den)
                     zeroZ_mem_IntSet hc_num_den hc_den_sq H_c (square_nonneg c_den hc_den_i)
      rw [mulZ_zero_right (mulZ c_den c_den) hc_den_sq,
          mulZ_comm (mulZ c_den c_den) (mulZ c_num c_den) hc_den_sq hc_num_den] at step
      exact step

    have H_ab_mul := mulZ_le_mulZ_nonneg
                       (mulZ (mulZ a_num a_den) (mulZ b_den b_den))
                       (mulZ (mulZ a_den a_den) (mulZ b_num b_den))
                       (mulZ (mulZ c_num c_den) (mulZ c_den c_den))
                       (mulZ_in_IntSet (mulZ a_num a_den) (mulZ b_den b_den)
                         (mulZ_in_IntSet a_num a_den ha_num ha_den_i)
                         (mulZ_in_IntSet b_den b_den hb_den_i hb_den_i))
                       (mulZ_in_IntSet (mulZ a_den a_den) (mulZ b_num b_den)
                         (mulZ_in_IntSet a_den a_den ha_den_i ha_den_i)
                         (mulZ_in_IntSet b_num b_den hb_num hb_den_i))
                       hc_mul H_ab hc_mul_nn
                       
    -- Now rewrite H_ab_mul to the goal.
    -- H_ab_mul is: Z * X <= Z * Y where Z = (c_num * c_den) * c_den^2.
    -- Goal is: X' <= Y' where X' = ((a_num * c_num) * (a_den * c_den)) * ((b_den * c_den) * (b_den * c_den)).
    
    have hab := mulZ_in_IntSet a_num a_den ha_num ha_den_i
    have hb2 := mulZ_in_IntSet b_den b_den hb_den_i hb_den_i
    have ha2 := mulZ_in_IntSet a_den a_den ha_den_i ha_den_i
    have hbc := mulZ_in_IntSet b_num b_den hb_num hb_den_i
    have hac_num := mulZ_in_IntSet a_num c_num ha_num hc_num
    have hac_den := mulZ_in_IntSet a_den c_den ha_den_i hc_den_i
    have hbc_den := mulZ_in_IntSet b_den c_den hb_den_i hc_den_i
    have hbc_num := mulZ_in_IntSet b_num c_num hb_num hc_num

    have h_lhs : mulZ (mulZ (mulZ c_num c_den) (mulZ c_den c_den))
                      (mulZ (mulZ a_num a_den) (mulZ b_den b_den)) =
                 mulZ (mulZ (mulZ a_num c_num) (mulZ a_den c_den))
                      (mulZ (mulZ b_den c_den) (mulZ b_den c_den)) := by
      calc mulZ (mulZ (mulZ c_num c_den) (mulZ c_den c_den))
                (mulZ (mulZ a_num a_den) (mulZ b_den b_den))
          = mulZ (mulZ (mulZ a_num a_den) (mulZ b_den b_den))
                 (mulZ (mulZ c_num c_den) (mulZ c_den c_den)) :=
              by rw [mulZ_comm (mulZ (mulZ c_num c_den) (mulZ c_den c_den))
                               (mulZ (mulZ a_num a_den) (mulZ b_den b_den))
                               hc_mul (mulZ_in_IntSet (mulZ a_num a_den) (mulZ b_den b_den) hab hb2)]
        _ = mulZ (mulZ (mulZ a_num a_den) (mulZ c_num c_den))
                 (mulZ (mulZ b_den b_den) (mulZ c_den c_den)) :=
              mul4_comm (mulZ a_num a_den) (mulZ b_den b_den)
                        (mulZ c_num c_den) (mulZ c_den c_den)
                        hab hb2 hc_num_den hc_den_sq
        _ = mulZ (mulZ (mulZ a_num c_num) (mulZ a_den c_den))
                 (mulZ (mulZ b_den b_den) (mulZ c_den c_den)) :=
              by rw [mul4_comm a_num a_den c_num c_den ha_num ha_den_i hc_num hc_den_i]
        _ = mulZ (mulZ (mulZ a_num c_num) (mulZ a_den c_den))
                 (mulZ (mulZ b_den c_den) (mulZ b_den c_den)) :=
              by rw [mul4_comm b_den b_den c_den c_den hb_den_i hb_den_i hc_den_i hc_den_i]

    have h_rhs : mulZ (mulZ (mulZ c_num c_den) (mulZ c_den c_den))
                      (mulZ (mulZ a_den a_den) (mulZ b_num b_den)) =
                 mulZ (mulZ (mulZ a_den c_den) (mulZ a_den c_den))
                      (mulZ (mulZ b_num c_num) (mulZ b_den c_den)) := by
      calc mulZ (mulZ (mulZ c_num c_den) (mulZ c_den c_den))
                (mulZ (mulZ a_den a_den) (mulZ b_num b_den))
          = mulZ (mulZ (mulZ a_den a_den) (mulZ b_num b_den))
                 (mulZ (mulZ c_num c_den) (mulZ c_den c_den)) :=
              by rw [mulZ_comm (mulZ (mulZ c_num c_den) (mulZ c_den c_den))
                               (mulZ (mulZ a_den a_den) (mulZ b_num b_den))
                               hc_mul (mulZ_in_IntSet (mulZ a_den a_den) (mulZ b_num b_den) ha2 hbc)]
        _ = mulZ (mulZ (mulZ a_den a_den) (mulZ b_num b_den))
                 (mulZ (mulZ c_den c_den) (mulZ c_num c_den)) :=
              by rw [mulZ_comm (mulZ c_num c_den) (mulZ c_den c_den) hc_num_den hc_den_sq]
        _ = mulZ (mulZ (mulZ a_den a_den) (mulZ c_den c_den))
                 (mulZ (mulZ b_num b_den) (mulZ c_num c_den)) :=
              mul4_comm (mulZ a_den a_den) (mulZ b_num b_den)
                        (mulZ c_den c_den) (mulZ c_num c_den)
                        ha2 hbc hc_den_sq hc_num_den
        _ = mulZ (mulZ (mulZ a_den c_den) (mulZ a_den c_den))
                 (mulZ (mulZ b_num b_den) (mulZ c_num c_den)) :=
              by rw [mul4_comm a_den a_den c_den c_den ha_den_i ha_den_i hc_den_i hc_den_i]
        _ = mulZ (mulZ (mulZ a_den c_den) (mulZ a_den c_den))
                 (mulZ (mulZ b_num c_num) (mulZ b_den c_den)) :=
              by rw [mul4_comm b_num b_den c_num c_den hb_num hb_den_i hc_num hc_den_i]

    rw [h_lhs, h_rhs] at H_ab_mul
    exact H_ab_mul

end ZFC.Rat.Field
